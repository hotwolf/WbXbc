//###############################################################################
//# WbXbc - Formal Testbench - Error Generator                                  #
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
//#    This is the the formal testbench for the WbXbc_error_generator           #
//#    component.                                                               #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   October 10, 2018                                                          #
//#      - Initial release                                                      #
//###############################################################################
`default_nettype none

//DUT configuration
//=================
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

module ftb_WbXbc_error_generator
   (//Clock and reset
    //---------------
    input wire                    clk_i,            //module clock
    input wire                    async_rst_i,      //asynchronous reset
    input wire                    sync_rst_i,       //synchronous reset
				  
    //Initiator interface	  
    //-------------------	  
    input  wire                   itr_cyc_i,        //bus cycle indicator       +-
    input  wire                   itr_stb_i,        //access request            |
    input  wire                   itr_we_i,         //write enable              |
    input  wire                   itr_lock_i,       //uninterruptable bus cycle | initiator
    input  wire [`SEL_WIDTH-1:0]  itr_sel_i,        //write data selects        | initiator
    input  wire [`ADR_WIDTH-1:0]  itr_adr_i,        //address bus               | to
    input  wire [`DAT_WIDTH-1:0]  itr_dat_i,        //write data bus            | target
    input  wire [`TGA_WIDTH-1:0]  itr_tga_i,        //address tags              |
    input  wire [`TGT_CNT-1:0]    itr_tga_tgtsel_i, //target select tags        |
    input  wire [`TGC_WIDTH-1:0]  itr_tgc_i,        //bus cycle tags            |
    input  wire [`TGWD_WIDTH-1:0] itr_tgd_i,        //write data tags           +-
    output wire                   itr_ack_o,        //bus cycle acknowledge     +-
    output wire                   itr_err_o,        //error indicator           | target
    output wire                   itr_rty_o,        //retry request             | to
    output wire                   itr_stall_o,      //access delay              | initiator
    output wire [`DAT_WIDTH-1:0]  itr_dat_o,        //read data bus             |
    output wire [`TGRD_WIDTH-1:0] itr_tgd_o,        //read data tags            +-

    //Target interface
    //----------------
    output wire                   tgt_cyc_o,        //bus cycle indicator       +-
    output wire                   tgt_stb_o,        //access request            |
    output wire                   tgt_we_o,         //write enable              |
    output wire                   tgt_lock_o,       //uninterruptable bus cycle |
    output wire [`SEL_WIDTH-1:0]  tgt_sel_o,        //write data selects        | initiator
    output wire [`ADR_WIDTH-1:0]  tgt_adr_o,        //write data selects        | to
    output wire [`DAT_WIDTH-1:0]  tgt_dat_o,        //write data bus            | target
    output wire [`TGA_WIDTH-1:0]  tgt_tga_o,        //address tags              |
    output wire [`TGT_CNT-1:0]    tgt_tga_tgtsel_o, //target select tags        |
    output wire [`TGC_WIDTH-1:0]  tgt_tgc_o,        //bus cycle tags            |
    output wire [`TGWD_WIDTH-1:0] tgt_tgd_o,        //write data tags           +-
    input  wire                   tgt_ack_i,        //bus cycle acknowledge     +-
    input  wire                   tgt_err_i,        //error indicator           | target
    input  wire                   tgt_rty_i,        //retry request             | to
    input  wire                   tgt_stall_i,      //access delay              | initiator
    input  wire [`DAT_WIDTH-1:0]  tgt_dat_i,        //read data bus             |
    input  wire [`TGRD_WIDTH-1:0] tgt_tgd_i);       //read data tags            +-

   //DUT
   //===
   WbXbc_error_generator #(.TGT_CNT   (`TGT_CNT   )
			   .ADR_WIDTH (`ADR_WIDTH )
			   .DAT_WIDTH (`DAT_WIDTH )
			   .SEL_WIDTH (`SEL_WIDTH )
			   .TGA_WIDTH (`TGA_WIDTH )
			   .TGC_WIDTH (`TGC_WIDTH )
			   .TGRD_WIDTH(`TGRD_WIDTH)
			   .TGWD_WIDTH(`TGWD_WIDTH)) DUT
     (.*);

   //Protocol assertions
   //===================
   wb_itr_mon #(.TGT_CNT   (`TGT_CNT   )
		.ADR_WIDTH (`ADR_WIDTH )
		.DAT_WIDTH (`DAT_WIDTH )
		.SEL_WIDTH (`SEL_WIDTH )
		.TGA_WIDTH (`TGA_WIDTH + TGT_CNT)
		.TGC_WIDTH (`TGC_WIDTH )
		.TGRD_WIDTH(`TGRD_WIDTH)
		.TGWD_WIDTH(`TGWD_WIDTH)) wb_itr_mon
     (.*,
      .itr_tga_i {itr_tga_tgtsel_i, itr_tga_i});
     
   wb_tgt_mon #(.TGT_CNT   (`TGT_CNT   )	    
	     	.ADR_WIDTH (`ADR_WIDTH )	    
	     	.DAT_WIDTH (`DAT_WIDTH )	    
	     	.SEL_WIDTH (`SEL_WIDTH )	    
	     	.TGA_WIDTH (`TGA_WIDTH + TGT_CNT)	    
	     	.TGC_WIDTH (`TGC_WIDTH )	    
	     	.TGRD_WIDTH(`TGRD_WIDTH)	    
	     	.TGWD_WIDTH(`TGWD_WIDTH)) wb_tgt_mon
     (.*,
      .tgt_tga_o {tgt_tga_tgtsel_o, tgt_tga_o});
     
   //Pass-through assertions
   //=======================
   wb_pass_through #(.TGT_CNT   (`TGT_CNT   )	     
		     .ADR_WIDTH (`ADR_WIDTH )	    
		     .DAT_WIDTH (`DAT_WIDTH )	    
		     .SEL_WIDTH (`SEL_WIDTH )	    
		     .TGA_WIDTH (`TGA_WIDTH + TGT_CNT )	    
		     .TGC_WIDTH (`TGC_WIDTH )	    
		     .TGRD_WIDTH(`TGRD_WIDTH)	    
		     .TGWD_WIDTH(`TGWD_WIDTH)) wb_pass_through
     (.*,
      .pass_through_en (|itr_tga_tgtsel_i),
      .itr_tga_i       ({itr_tga_tgtsel_i, itr_tga_i}),
      .tgt_tga_o       ({tgt_tga_tgtsel_o, tgt_tga_o}));

   //Additional assertions
   //=====================
   //Error response to access without target
   property p_err_resp;
      @(posedge clk_i) disable iff (async_rst_i|sync_rst_i)
	&{itr_cyc_i, itr_stb_i, ~|itr_tga_tgtsel_i} |=> itr_err_o;
   endproperty // p_err_resp
   a_err_resp: assert property (p_err_resp);

endmodule // ftb_WbXbc_error_generator
