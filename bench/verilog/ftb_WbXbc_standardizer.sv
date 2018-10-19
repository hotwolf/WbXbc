//###############################################################################
//# WbXbc - Formal Testbench - Pipelined to Standard Bus Gasket                 #
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
//#    This is the the formal testbench for the WbXbc_standardizer component.   #
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

module ftb_WbXbc_standardizer
   (//Clock and reset
    //---------------
    input wire                       clk_i,              //module clock
    input wire                       async_rst_i,        //asynchronous reset
    input wire                       sync_rst_i,         //synchronous reset

    //Initiator interface
    //-------------------
    input  wire                      itr_cyc_i,          //bus cycle indicator       +-
    input  wire                      itr_stb_i,          //access request            |
    input  wire                      itr_we_i,           //write enable              |
    input  wire                      itr_lock_i,         //uninterruptable bus cycle | initiator
    input  wire [`SEL_WIDTH-1:0]     itr_sel_i,          //write data selects        | to
    input  wire [`ADR_WIDTH-1:0]     itr_adr_i,          //address bus               | target
    input  wire [`DAT_WIDTH-1:0]     itr_dat_i,          //write data bus            |
    input  wire [`TGA_WIDTH-1:0]     itr_tga_i,          //address tags              |
    input  wire [`TGC_WIDTH-1:0]     itr_tgc_i,          //bus cycle tags            |
    input  wire [`TGWD_WIDTH-1:0]    itr_tgd_i,          //write data tags           +-
    output wire                      itr_ack_o,          //bus cycle acknowledge     +-
    output wire                      itr_err_o,          //error indicator           | target
    output wire                      itr_rty_o,          //retry request             | to
    output wire                      itr_stall_o,        //access delay              | initiator
    output wire [`DAT_WIDTH-1:0]     itr_dat_o,          //read data bus             |
    output wire [`TGRD_WIDTH-1:0]    itr_tgd_o,          //read data tags            +-

    //Target interface
    //----------------
    output wire                      tgt_cyc_o,          //bus cycle indicator       +-
    output wire                      tgt_stb_o,          //access request            |
    output wire                      tgt_we_o,           //write enable              |
    output wire                      tgt_lock_o,         //uninterruptable bus cycle | initiator
    output wire [`SEL_WIDTH-1:0]     tgt_sel_o,          //write data selects        | to
    output wire [`ADR_WIDTH-1:0]     tgt_adr_o,          //write data selects        | target
    output wire [`DAT_WIDTH-1:0]     tgt_dat_o,          //write data bus            |
    output wire [`TGA_WIDTH-1:0]     tgt_tga_o,          //address tags              |
    output wire [`TGC_WIDTH-1:0]     tgt_tgc_o,          //bus cycle tags            |
    output wire [`TGWD_WIDTH-1:0]    tgt_tgd_o,          //write data tags           +-
    input  wire                      tgt_ack_i,          //bus cycle acknowledge     +-
    input  wire                      tgt_err_i,          //error indicator           | target
    input  wire                      tgt_rty_i,          //retry request             | to
    input  wire                      tgt_stall_i,        //access delay              | initiator
    input  wire [`DAT_WIDTH-1:0]     tgt_dat_i,          //read data bus             |
    input  wire [`TGRD_WIDTH-1:0]    tgt_tgd_i);         //read data tags            +-

   //DUT
   //===
   WbXbc_standardizer
     #(.ADR_WIDTH     (`ADR_WIDTH),                      //width of the address bus
       .DAT_WIDTH     (`DAT_WIDTH),                      //width of each data bus
       .SEL_WIDTH     (`SEL_WIDTH),                      //number of data select lines
       .TGA_WIDTH     (`TGA_WIDTH),                      //number of propagated address tags
       .TGC_WIDTH     (`TGC_WIDTH),                      //number of propagated cycle tags
       .TGRD_WIDTH    (`TGRD_WIDTH),                     //number of propagated read data tags
       .TGWD_WIDTH    (`TGWD_WIDTH))                     //number of propagated write data tags
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
//   initial assume property (async_rst_i);                //asynchronous rese
//   initial assume property (sync_rst_i);                 //synchronous reset
//
//   //Protocol assertions
//   //===================
//   wb_itr_mon
//     #(.ADR_WIDTH (`ADR_WIDTH),                          //width of the address bus
//       .DAT_WIDTH (`DAT_WIDTH),                          //width of each data bus
//       .SEL_WIDTH (`SEL_WIDTH),                          //number of data select lines
//       .TGA_WIDTH (`TGA_WIDTH + `TGT_CNT),               //number of propagated address tags
//       .TGC_WIDTH (`TGC_WIDTH),                          //number of propagated cycle tags
//       .TGRD_WIDTH(`TGRD_WIDTH),                         //number of propagated read data tags
//       .TGWD_WIDTH(`TGWD_WIDTH))                         //number of propagated write data tags
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
//   wb_tgt_mon
//     #(.ADR_WIDTH (`ADR_WIDTH),                          //width of the address bus
//       .DAT_WIDTH (`DAT_WIDTH),                          //width of each data bus
//       .SEL_WIDTH (`SEL_WIDTH),                          //number of data select lines
//       .TGA_WIDTH (`TGA_WIDTH + `TGT_CNT),               //number of propagated address tags
//       .TGC_WIDTH (`TGC_WIDTH),                          //number of propagated cycle tags
//       .TGRD_WIDTH(`TGRD_WIDTH),                         //number of propagated read data tags
//       .TGWD_WIDTH(`TGWD_WIDTH))                         //number of propagated write data tags
//   wb_tgt_mon
//     (//Clock and reset
//      //---------------
//      .clk_i            (clk_i),                         //module clock
//      .async_rst_i      (async_rst_i),                   //asynchronous reset
//      .sync_rst_i       (sync_rst_i),                    //synchronous reset
//
//      //Target interface
//      //----------------
//      .tgt_cyc_o        (tgt_cyc_o),                     //bus cycle indicator       +-
//      .tgt_stb_o        (tgt_stb_o),                     //access request            |
//      .tgt_we_o         (tgt_we_o),                      //write enable              |
//      .tgt_lock_o       (tgt_lock_o),                    //uninterruptable bus cycle |
//      .tgt_sel_o        (tgt_sel_o),                     //write data selects        | initiator
//      .tgt_adr_o        (tgt_adr_o),                     //write data selects        | to
//      .tgt_dat_o        (tgt_dat_o),                     //write data bus            | target
//      .tgt_tga_o        ({tgt_tga_tgtsel_o, tgt_tga_o}), //address tags              |
//      .tgt_tgc_o        (tgt_tgc_o),                     //bus cycle tags            |
//      .tgt_tgd_o        (tgt_tgd_o),                     //write data tags           +-
//      .tgt_ack_i        (tgt_ack_i),                     //bus cycle acknowledge     +-
//      .tgt_err_i        (tgt_err_i),                     //error indicator           | target
//      .tgt_rty_i        (tgt_rty_i),                     //retry request             | to
//      .tgt_stall_i      (tgt_stall_i),                   //access delay              | initiator
//      .tgt_dat_i        (tgt_dat_i),                     //read data bus             |
//      .tgt_tgd_i        (tgt_tgd_i));                    //read data tags            +-
//
//   //Pass-through assertions
//   //=======================
//   wb_pass_through
//     #(.ADR_WIDTH (`ADR_WIDTH),                          //width of the address bus
//       .DAT_WIDTH (`DAT_WIDTH),                          //width of each data bus
//       .SEL_WIDTH (`SEL_WIDTH),                          //number of data select lines
//       .TGA_WIDTH (`TGA_WIDTH + `TGT_CNT),               //number of propagated address tags
//       .TGC_WIDTH (`TGC_WIDTH),                          //number of propagated cycle tags
//       .TGRD_WIDTH(`TGRD_WIDTH),                         //number of propagated read data tags
//       .TGWD_WIDTH(`TGWD_WIDTH))                         //number of propagated write data tags
//   wb_pass_through
//     (//Assertion control
//      //-----------------
//      .pass_through_en (|itr_tga_tgtsel_i),
//
//      //Clock and reset
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
//      .itr_lock_i       (itr_lock_i),                    //uninterruptable bus cycle | initiator
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
//      .itr_tgd_o        (itr_tgd_o),                     //read data tags            +-
//
//      //Target interface
//      //----------------
//      .tgt_cyc_o        (tgt_cyc_o),                     //bus cycle indicator       +-
//      .tgt_stb_o        (tgt_stb_o),                     //access request            |
//      .tgt_we_o         (tgt_we_o),                      //write enable              |
//      .tgt_lock_o       (tgt_lock_o),                    //uninterruptable bus cycle |
//      .tgt_sel_o        (tgt_sel_o),                     //write data selects        | initiator
//      .tgt_adr_o        (tgt_adr_o),                     //write data selects        | to
//      .tgt_dat_o        (tgt_dat_o),                     //write data bus            | target
//      .tgt_tga_o        ({tgt_tga_tgtsel_o, tgt_tga_o}), //address tags              |
//      .tgt_tgc_o        (tgt_tgc_o),                     //bus cycle tags            |
//      .tgt_tgd_o        (tgt_tgd_o),                     //write data tags           +-
//      .tgt_ack_i        (tgt_ack_i),                     //bus cycle acknowledge     +-
//      .tgt_err_i        (tgt_err_i),                     //error indicator           | target
//      .tgt_rty_i        (tgt_rty_i),                     //retry request             | to
//      .tgt_stall_i      (tgt_stall_i),                   //access delay              | initiator
//      .tgt_dat_i        (tgt_dat_i),                     //read data bus             |
//      .tgt_tgd_i        (tgt_tgd_i));                    //read data tags            +-
//
//   //Additional assertions
//   //=====================
//
//   //Abbreviations
//   wire                  rst       = |{async_rst_i, sync_rst_i};            //reset
//   wire                  req       = &{~itr_stall_o, itr_cyc_i, itr_stb_i}; //request
//   wire                  no_tgt    = ~|{itr_tga_tgtsel_i};                  //no target
//   wire                  inval_req = &{req, no_tgt};                        //invalid request
//   wire                  val_req   = &{req, ~no_tgt};                       //valid request
//   wire                  ack       = |{itr_ack_o, itr_err_o, itr_rty_o};    //acknowledge
//
//   //State Machine
//   //=============
//    //                             inval_req     _______
//   //                      +------------------->/       \
//   //                      |                    | ERROR |
//   //                      |  +-----------------\_______/
//   //                      |  |   ~req & ack      ^  |
//   //        _______      _|__v_                  |  |
//   // rst   /       \    /      \        inval_req|  |val_req
//   //  O--->| RESET |--->| IDLE |               & |  | &
//   //       \_______/    \______/              ack|  |ack
//   //                      ^  |                   |  |
//   //                      |  |    val_req       _|__v_
//   //                      |  +---------------->/      \
//   //                      |                    | BUSY |
//   //                      +--------------------\______/
//   //                             ~req & ack
//   //State encoding
//   parameter STATE_RESET = 2'b00;
//   parameter STATE_IDLE  = 2'b01;
//   parameter STATE_BUSY  = 2'b10;
//   parameter STATE_ERROR = 2'b11;
//   //State variable
//   reg          [1:0]                           state_reg;
//   wire         [1:0]                           state_next;
//   always @(posedge async_rst_i or posedge clk_i)
//     if (async_rst_i)                                        //asynchronous reset
//       state_reg <= STATE_RESET;
//     else if (sync_rst_i)                                    //synchronous reset
//       state_reg <= STATE_RESET;
//     else
//       state_reg <= state_next;                              //state transition
//   //State transitions
//   always @*
//     begin
//        //Default transition
//        state_next = state_reg; //remain in current state
//        case (state_reg)
//          STATE_RESET:
//            begin
//               state_next = STATE_IDLE;
//            end
//          STATE_IDLE:
//            begin
//               if (val_req)
//                 state_next = STATE_BUSY;
//               if (inval_req)
//                 state_next = STATE_ERROR;
//            end
//          STATE_BUSY:
//            begin
//               if (~req & ack)
//                 state_next = STATE_IDLE;
//               if (inval_req & ack)
//                 state_next = STATE_ERROR;
//            end
//          STATE_ERROR:
//            begin
//               if (~req & ack)
//                 state_next = STATE_IDLE;
//               if (val_req & ack)
//                 state_next = STATE_BUSY;
//            end
//        endcase // case (state_reg)
//     end // always @ *
//
//   //Error response rules
//   //====================
//   always @(posedge clk_i)
//     begin
//        //Get an error reponse one clock cycle after the request
//        if (state_reg == STATE_ERROR)
//          begin
//             assert property (itr_err_o);
//          end // if (state_reg == STATE_ERROR)
//        //Don't pass through invalid requests
//        if (inval_req)
//          begin
//             assert property (~&{tgt_cyc_o, tgt_stb_o});
//          end // if (inval_req)
//     end // always @ (posedge clk_i)
//
//   //Cover valid state transitions
//   //=============================
//   always @(posedge clk_i)
//     begin
//        cover property (($past(state_reg) == STATE_IDLE)  && (state_reg == STATE_BUSY));  //IDLE  -> BUSY
//        cover property (($past(state_reg) == STATE_BUSY)  && (state_reg == STATE_IDLE));  //BUSY  -> IDLE
//        cover property (($past(state_reg) == STATE_IDLE)  && (state_reg == STATE_ERROR)); //IDLE  -> ERROR
//        cover property (($past(state_reg) == STATE_ERROR) && (state_reg == STATE_IDLE));  //ERROR -> IDLE
//        cover property (($past(state_reg) == STATE_BUSY)  && (state_reg == STATE_ERROR)); //BUSY  -> ERROR
//        cover property (($past(state_reg) == STATE_ERROR) && (state_reg == STATE_BUSY));  //ERROR -> BUSY
//     end // always @ (posedge clk_i)
//
`endif //  `ifdef FORMAL

endmodule // ftb_WbXbc_standardizer
