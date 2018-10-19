//###############################################################################
//# WbXbc - Formal Testbench - Plain Crossbar Switch                            #
//###############################################################################
//#    Copyright 2018 Dirk Heisswolf                                            #
//#    This file is part of the WbXbc project.                                  #
//#                                                                             #
//#    WbXbc is free software: you can redistribute it and/or modify            #
//#    it under the terms of the GNU General Public License as published by     #
//#    the Free Software Foundation, either version 3 of the License, or        #
//#    (at your option) any later version.                                      #
//#                                                                             #
//#    WbXbc is distributed in the hope that it will be useful,                 #
//#    but WITHOUT ANY WARRANTY; without even the implied warranty of           #
//#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            #
//#    GNU General Public License for more details.                             #
//#                                                                             #
//#    You should have received a copy of the GNU General Public License        #
//#    along with WbXbc.  If not, see <http://www.gnu.org/licenses/>.           #
//###############################################################################
//# Description:                                                                #
//#    This is the the formal testbench for the WbXbc_xbar component.           #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   October 19, 2018                                                          #
//#      - Initial release                                                      #
//###############################################################################
`default_nettype none

//DUT configuration
//=================
//Default configuration
//---------------------
`ifndef CONF_DEFAULT
`endif

//Fall back
//---------
`ifndef ITR_CNT
`define ITR_CNT     4
`endif
`ifndef TGT_CNT
`define TGT_CNT     4
`endif
`ifndef ADR_WIDTH
`define ADR_WIDTH   16
`endif
`ifndef DAT_WIDTH
`define DAT_WIDTH   16
`endif
`ifndef SEL_WIDTH
`define SEL_WIDTH   2
`endif
`ifndef TGA_WIDTH
`define TGA_WIDTH   1
`endif
`ifndef TGC_WIDTH
`define TGC_WIDTH   1
`endif
`ifndef TGRD_WIDTH
`define TGRD_WIDTH  1
`endif
`ifndef TGWD_WIDTH
`define TGWD_WIDTH  1
`endif

module ftb_WbXbc_xbar
   (//Clock and reset
    //---------------
    input wire                               clk_i,            //module clock
    input wire                               async_rst_i,      //asynchronous reset
    input wire                               sync_rst_i,       //synchronous reset
                                  		
    //Initiator interface         		
    //-------------------         		
    input  wire [`ITR_CNT-1:0]               itr_cyc_i,        //bus cycle indicator       +-
    input  wire [`ITR_CNT-1:0]               itr_stb_i,        //access request            |
    input  wire [`ITR_CNT-1:0]               itr_we_i,         //write enable              |
    input  wire [`ITR_CNT-1:0]               itr_lock_i,       //uninterruptable bus cycle |
    input  wire [(`ITR_CNT*`SEL_WIDTH)-1:0]  itr_sel_i,        //write data selects        | initiator
    input  wire [(`ITR_CNT*`ADR_WIDTH)-1:0]  itr_adr_i,        //address bus               | to
    input  wire [(`ITR_CNT*`DAT_WIDTH)-1:0]  itr_dat_i,        //write data bus            | target
    input  wire [(`ITR_CNT*`TGA_WIDTH)-1:0]  itr_tga_i,        //address tags              |
    input  wire [`ITR_CNT-1:0]               itr_tga_prio_i,   //access priorities         |
    input  wire [(`ITR_CNT*`TGC_WIDTH)-1:0]  itr_tgc_i,        //bus cycle tags            |
    input  wire [(`ITR_CNT*`TGWD_WIDTH)-1:0] itr_tgd_i,        //write data tags           +-
    output wire [`ITR_CNT-1:0]               itr_ack_o,        //bus cycle acknowledge     +-
    output wire [`ITR_CNT-1:0]               itr_err_o,        //error indicator           | target
    output wire [`ITR_CNT-1:0]               itr_rty_o,        //retry request             | to
    output wire [`ITR_CNT-1:0]               itr_stall_o,      //access delay              | initiator
    output wire [(`ITR_CNT*`DAT_WIDTH)-1:0]  itr_dat_o,        //read data bus             |
    output wire [(`ITR_CNT*`TGRD_WIDTH)-1:0] itr_tgd_o,        //read data tags            +-

    //Target interface
    //----------------
    output wire [`TGT_CNT-1:0]               tgt_cyc_o,        //bus cycle indicator       +-
    output wire [`TGT_CNT-1:0]               tgt_stb_o,        //access request            |
    output wire [`TGT_CNT-1:0]               tgt_we_o,         //write enable              |
    output wire [`TGT_CNT-1:0]               tgt_lock_o,       //uninterruptable bus cycle |
    output wire [(`TGT_CNT*`SEL_WIDTH)-1:0]  tgt_sel_o,        //write data selects        | initiator
    output wire [(`TGT_CNT*`ADR_WIDTH)-1:0]  tgt_adr_o,        //write data selects        | to
    output wire [(`TGT_CNT*`DAT_WIDTH)-1:0]  tgt_dat_o,        //write data bus            | target
    output wire [(`TGT_CNT*`TGA_WIDTH)-1:0]  tgt_tga_o,        //address tags              |
    output wire [(`TGT_CNT*`TGC_WIDTH)-1:0]  tgt_tgc_o,        //bus cycle tags            |
    output wire [(`TGT_CNT*`TGWD_WIDTH)-1:0] tgt_tgd_o,        //write data tags           +-
    input  wire [`TGT_CNT-1:0]               tgt_ack_i,        //bus cycle acknowledge     +-
    input  wire [`TGT_CNT-1:0]               tgt_err_i,        //error indicator           | target
    input  wire [`TGT_CNT-1:0]               tgt_rty_i,        //retry request             | to
    input  wire [`TGT_CNT-1:0]               tgt_stall_i,      //access delay              | initiator
    input  wire [(`TGT_CNT*`DAT_WIDTH)-1:0]  tgt_dat_i,        //read data bus             |
    input  wire [(`TGT_CNT*`TGRD_WIDTH)-1:0] tgt_tgd_i);       //read data tags            +-
						
   //DUT					
   //===					
   WbXbc_xbar			
     #(.ITR_CNT   (`ITR_CNT),                            //number of initiator addresses
       .ITR_CNT   (`TGT_CNT),                            //number of target addresses
       .ADR_WIDTH (`ADR_WIDTH),                          //width of the address bus
       .DAT_WIDTH (`DAT_WIDTH),                          //width of each data bus
       .SEL_WIDTH (`SEL_WIDTH),                          //number of data select lines
       .TGA_WIDTH (`TGA_WIDTH),                          //number of propagated address tags
       .TGC_WIDTH (`TGC_WIDTH),                          //number of propagated cycle tags
       .TGRD_WIDTH(`TGRD_WIDTH),                         //number of propagated read data tags
       .TGWD_WIDTH(`TGWD_WIDTH))                         //number of propagated write data tags
   DUT
     (//Clock and reset
      //---------------
      .clk_i            (clk_i),                         //module clock
      .async_rst_i      (async_rst_i),                   //asynchronous reset
      .sync_rst_i       (sync_rst_i),                    //synchronous reset
      
      //Initiator interface		
      //-------------------		
      .itr_cyc_i        (itr_cyc_i),                     //bus cycle indicator       +-
      .itr_stb_i        (itr_stb_i),                     //access request            |
      .itr_we_i         (itr_we_i),                      //write enable              |
      .itr_lock_i       (itr_lock_i),                    //uninterruptable bus cycle |
      .itr_sel_i        (itr_sel_i),                     //write data selects        | initiator
      .itr_adr_i        (itr_adr_i),                     //address bus               | to
      .itr_dat_i        (itr_dat_i),                     //write data bus            | target
      .itr_tga_i        (itr_tga_i),                     //address tags              |
      .itr_tga_prio_i   (itr_tga_prio_i),                //access priorities         |
      .itr_tgc_i        (itr_tgc_i),                     //bus cycle tags            |
      .itr_tgd_i        (itr_tgd_i),                     //write data tags           +-
      .itr_ack_o        (itr_ack_o),                     //bus cycle acknowledge     +-
      .itr_err_o        (itr_err_o),                     //error indicator           | target
      .itr_rty_o        (itr_rty_o),                     //retry request             | to
      .itr_stall_o      (itr_stall_o),                   //access delay              | initiator
      .itr_dat_o        (itr_dat_o),                     //read data bus             |
      .itr_tgd_o        (itr_tgd_o),                     //read data tags            +-

      //Target interface
      //----------------
      .tgt_cyc_o        (tgt_cyc_o),                     //bus cycle indicator       +-
      .tgt_stb_o        (tgt_stb_o),                     //access request            |
      .tgt_we_o         (tgt_we_o),                      //write enable              |
      .tgt_lock_o       (tgt_lock_o),                    //uninterruptable bus cycle |
      .tgt_sel_o        (tgt_sel_o),                     //write data selects        | initiator
      .tgt_adr_o        (tgt_adr_o),                     //write data selects        | to
      .tgt_dat_o        (tgt_dat_o),                     //write data bus            | target
      .tgt_tga_o        (tgt_tga_o),                     //address tags              |
      .tgt_tgc_o        (tgt_tgc_o),                     //bus cycle tags            |
      .tgt_tgd_o        (tgt_tgd_o),                     //write data tags           +-
      .tgt_ack_i        (tgt_ack_i),                     //bus cycle acknowledge     +-
      .tgt_err_i        (tgt_err_i),                     //error indicator           | target
      .tgt_rty_i        (tgt_rty_i),                     //retry request             | to
      .tgt_stall_i      (tgt_stall_i),                   //access delay              | initiator
      .tgt_dat_i        (tgt_dat_i),                     //read data bus             |
      .tgt_tgd_i        (tgt_tgd_i));                    //read data tags            +-

`ifdef FORMAL
//   //Reset condition
//   //===============
//   initial assume property (~clk_i);                     //module clock	
//   initial assume property (async_rst_i);  		 //asynchronous rese
//   initial assume property (sync_rst_i);		 //synchronous reset
//   
//   //Protocol assertions
//   //===================
//   wb_itr_mon
//     #(.ADR_WIDTH (`ADR_WIDTH),			         //width of the address bus
//       .DAT_WIDTH (`DAT_WIDTH),			         //width of each data bus
//       .SEL_WIDTH (`SEL_WIDTH),			         //number of data select lines
//       .TGA_WIDTH (`TGA_WIDTH + `TGT_CNT),	         //number of propagated address tags
//       .TGC_WIDTH (`TGC_WIDTH),			         //number of propagated cycle tags
//       .TGRD_WIDTH(`TGRD_WIDTH),		         //number of propagated read data tags
//       .TGWD_WIDTH(`TGWD_WIDTH))		         //number of propagated write data tags
//   wb_itr_mon
//     (//Clock and reset
//      //---------------
//      .clk_i            (clk_i),                         //module clock
//      .async_rst_i      (async_rst_i),                   //asynchronous reset
//      .sync_rst_i       (sync_rst_i),                    //synchronous reset
//
//      //Initiator interface
//      //-------------------
//      .itr_cyc_i        (itr_cyc_i),                     //bus cycle indicator       +-
//      .itr_stb_i        (itr_stb_i),                     //access request            |
//      .itr_we_i         (itr_we_i),                      //write enable              |
//      .itr_lock_i       (itr_lock_i),                    //uninterruptable bus cycle |
//      .itr_sel_i        (itr_sel_i),                     //write data selects        | initiator
//      .itr_adr_i        (itr_adr_i),                     //address bus               | to
//      .itr_dat_i        (itr_dat_i),                     //write data bus            | target
//      .itr_tga_i        ({itr_tga_tgtsel_i, itr_tga_i}), //address tags              |
//      .itr_tgc_i        (itr_tgc_i),                     //bus cycle tags            |
//      .itr_tgd_i        (itr_tgd_i),                     //write data tags           +-
//      .itr_ack_o        (itr_ack_o),                     //bus cycle acknowledge     +-
//      .itr_err_o        (itr_err_o),                     //error indicator           | target
//      .itr_rty_o        (itr_rty_o),                     //retry request             | to
//      .itr_stall_o      (itr_stall_o),                   //access delay              | initiator
//      .itr_dat_o        (itr_dat_o),                     //read data bus             |
//      .itr_tgd_o        (itr_tgd_o));                    //read data tags            +-
//   
//   genvar 				     i;
//
//   generate
//      for (i=0; i<`TGT_CNT; i=i+1)
//	begin
//   
//	   wb_tgt_mon
//	     #(.ADR_WIDTH (`ADR_WIDTH),     			                   //width of the address bus
//	       .DAT_WIDTH (`DAT_WIDTH),     			                   //width of each data bus
//	       .SEL_WIDTH (`SEL_WIDTH),     			                   //number of data select lines
//	       .TGA_WIDTH (`TGA_WIDTH),           	                           //number of propagated address tags
//	       .TGC_WIDTH (`TGC_WIDTH),     			                   //number of propagated cycle tags
//	       .TGRD_WIDTH(`TGRD_WIDTH),            		                   //number of propagated read data tags
//	       .TGWD_WIDTH(`TGWD_WIDTH))			                   //number of propagated write data tags
//	   wb_tgt_mon
//	     (//Clock and reset
//	      //---------------
//	      .clk_i            (clk_i),                                           //module clock
//	      .async_rst_i      (async_rst_i),                                     //asynchronous reset
//	      .sync_rst_i       (sync_rst_i),                                      //synchronous reset
//	      
//	      //Target interface
//	      //----------------
//	      .tgt_cyc_o        (tgt_cyc_o[i]),                                    //bus cycle indicator       +-
//	      .tgt_stb_o        (tgt_stb_o[i]),                                    //access request            |
//	      .tgt_we_o         (tgt_we_o[i]),                                     //write enable              |
//	      .tgt_lock_o       (tgt_lock_o[i]),                                   //uninterruptable bus cycle |
//	      .tgt_sel_o        (tgt_sel_o[((i+1)*`SEL_WIDTH)-1:i*`SEL_WIDTH]),    //write data selects        | initiator
//	      .tgt_adr_o        (tgt_adr_o[((i+1)*`ADR_WIDTH)-1:i*`ADR_WIDTH]),    //write data selects        | to
//	      .tgt_dat_o        (tgt_dat_o[((i+1)*`DAT_WIDTH)-1:i*`DAT_WIDTH]),    //write data bus            | target
//	      .tgt_tga_o        (tgt_tga_o[((i+1)*`TGA_WIDTH)-1:i*`TGA_WIDTH]),    //address tags              |
//	      .tgt_tgc_o        (tgt_tgc_o[((i+1)*`TGC_WIDTH)-1:i*`TGC_WIDTH]),    //bus cycle tags            |
//	      .tgt_tgd_o        (tgt_tgd_o[((i+1)*`TGWD_WIDTH)-1:i*`TGWD_WIDTH]),  //write data tags           +-
//	      .tgt_ack_i        (tgt_ack_i[i]),                                    //bus cycle acknowledge     +-
//	      .tgt_err_i        (tgt_err_i[i]),                                    //error indicator           | target
//	      .tgt_rty_i        (tgt_rty_i[i]),                                    //retry request             | to
//	      .tgt_stall_i      (tgt_stall_i[i]),                                  //access delay              | initiator
//	      .tgt_dat_i        (tgt_dat_i[((i+1)*`DAT_WIDTH)-1:i*`DAT_WIDTH]),    //read data bus             |
//	      .tgt_tgd_i        (tgt_tgd_i[((i+1)*`TGRD_WIDTH)-1:i*`TGRD_WIDTH])); //read data tags            +-
//	   
//	   //Pass-through assertions
//	   //=======================
//	   wb_pass_through
//	     #(.ADR_WIDTH (`ADR_WIDTH),     			                   //width of the address bus
//	       .DAT_WIDTH (`DAT_WIDTH),     			                   //width of each data bus
//	       .SEL_WIDTH (`SEL_WIDTH),     			                   //number of data select lines
//	       .TGA_WIDTH (`TGA_WIDTH),             	                           //number of propagated address tags
//	       .TGC_WIDTH (`TGC_WIDTH),     			                   //number of propagated cycle tags
//	       .TGRD_WIDTH(`TGRD_WIDTH),            		                   //number of propagated read data tags
//	       .TGWD_WIDTH(`TGWD_WIDTH))			                   //number of propagated write data tags
//	   wb_pass_through					                   
//	     (//Assertion control				                   
//	      //-----------------				                   
//	      .pass_through_en  (itr_tga_tgtsel_i[i]),		                   
//	      							                   
//	      //Clock and reset					                   
//	      //---------------					                   
//	      .clk_i            (clk_i),                                           //module clock
//	      .async_rst_i      (async_rst_i),                                     //asynchronous reset
//	      .sync_rst_i       (sync_rst_i),                                      //synchronous reset
//	      									   
//	      //Initiator interface						   
//	      //-------------------						   
//	      .itr_cyc_i        (itr_cyc_i),                                       //bus cycle indicator       +-
//	      .itr_stb_i        (itr_stb_i),                                       //access request            |
//	      .itr_we_i         (itr_we_i),                                        //write enable              |
//	      .itr_lock_i       (itr_lock_i),                                      //uninterruptable bus cycle | initiator
//	      .itr_sel_i        (itr_sel_i),                                       //write data selects        | initiator
//	      .itr_adr_i        (itr_adr_i),                                       //address bus               | to
//	      .itr_dat_i        (itr_dat_i),                                       //write data bus            | target
//	      .itr_tga_i        (itr_tga_i),                                       //address tags              |
//	      .itr_tgc_i        (itr_tgc_i),                                       //bus cycle tags            |
//	      .itr_tgd_i        (itr_tgd_i),                                       //write data tags           +-
//	      .itr_ack_o        (itr_ack_o),                                       //bus cycle acknowledge     +-
//	      .itr_err_o        (itr_err_o),                                       //error indicator           | target
//	      .itr_rty_o        (itr_rty_o),                                       //retry request             | to
//	      .itr_stall_o      (itr_stall_o),                                     //access delay              | initiator
//	      .itr_dat_o        (itr_dat_o),                                       //read data bus             |
//	      .itr_tgd_o        (itr_tgd_o));                                      //read data tags            +-
//	      			                   
//	      //Target interface
//	      //----------------
//	      .tgt_cyc_o        (tgt_cyc_o[i]),                                    //bus cycle indicator       +-
//	      .tgt_stb_o        (tgt_stb_o[i]),                                    //access request            |
//	      .tgt_we_o         (tgt_we_o[i]),                                     //write enable              |
//	      .tgt_lock_o       (tgt_lock_o[i]),                                   //uninterruptable bus cycle |
//	      .tgt_sel_o        (tgt_sel_o[((i+1)*`SEL_WIDTH)-1:i*`SEL_WIDTH]),    //write data selects        | initiator
//	      .tgt_adr_o        (tgt_adr_o[((i+1)*`ADR_WIDTH)-1:i*`ADR_WIDTH]),    //write data selects        | to
//	      .tgt_dat_o        (tgt_dat_o[((i+1)*`DAT_WIDTH)-1:i*`DAT_WIDTH]),    //write data bus            | target
//	      .tgt_tga_o        (tgt_tga_o[((i+1)*`TGA_WIDTH)-1:i*`TGA_WIDTH]),    //address tags              |
//	      .tgt_tgc_o        (tgt_tgc_o[((i+1)*`TGC_WIDTH)-1:i*`TGC_WIDTH]),    //bus cycle tags            |
//	      .tgt_tgd_o        (tgt_tgd_o[((i+1)*`TGWD_WIDTH)-1:i*`TGWD_WIDTH]),  //write data tags           +-
//	      .tgt_ack_i        (tgt_ack_i[i]),                                    //bus cycle acknowledge     +-
//	      .tgt_err_i        (tgt_err_i[i]),                                    //error indicator           | target
//	      .tgt_rty_i        (tgt_rty_i[i]),                                    //retry request             | to
//	      .tgt_stall_i      (tgt_stall_i[i]),                                  //access delay              | initiator
//	      .tgt_dat_i        (tgt_dat_i[((i+1)*`DAT_WIDTH)-1:i*`DAT_WIDTH]),    //read data bus             |
//	      .tgt_tgd_i        (tgt_tgd_i[((i+1)*`TGRD_WIDTH)-1:i*`TGRD_WIDTH])); //read data tags            +-
//
//	end // for (i=0; i<`TGT_CNT; i=i+1)
//   endgenerate
//   	   
//   //Additional assertions
//   //=====================
//
//   //Abbreviations
//   wire                                    itr_req = &{~itr_stall_o, itr_cyc_i, itr_stb_i}; //request
//   wire                                    tgt_req = {`TGT_CNT{~itr_stall_o}} & tgt_cyc_o & tgt_stb_o; //request
//
//   //Detect unexpected target accesses
//   //=================================
//   always @(posedge clk_i)
//     begin
//	//Initiator access must the passed on to only one target
//	assert property (itr_req == ~|(itr_tga_tgtsel_i ^ tgt_req));
//     end // always @ (posedge clk_i)
// 
//   //Cover all target accesses
//   //=========================
//   always @(posedge clk_i)
//     begin
//	for (int j = 1; j < `TGT_CNT; j=j+1)
//	  cover property (tgt_req[j]);
//     end // always @ (posedge clk_i) 
`endif //  `ifdef FORMAL

endmodule // ftb_WbXbc_xbar
