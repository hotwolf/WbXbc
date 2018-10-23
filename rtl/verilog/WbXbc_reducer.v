//###############################################################################
//# WbXbc - Wishbone Crossbar Components - Bus Width Reducer                    #
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
//#    This module connects a pipelined Wishbone initiator to a target with     #
//#    narrower data busses (half the width of the initiator's data busses).    #
//#    Initiator bus accesses may be converted into two consecutive accesses to #
//#    the target bus.                                                          #
//#                                                                             #
//#                          +-------------------+                              #
//#                          |                   |                              #
//#                          |                   |                              #
//#              wide        |       WbXbc       |     narrow                   #
//#            initiator --->|      reducer      |---> target                   #
//#               bus        |                   |      bus                     #
//#                          |                   |                              #
//#                          |                   |                              #
//#                          +-------------------+                              #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   July 30, 2018                                                             #
//#      - Initial release                                                      #
//#   October 8, 2018                                                           #
//#      - Updated parameter and signal naming                                  #
//###############################################################################
`default_nettype none

module WbXbc_reducer
  #(parameter ITR_ADR_WIDTH   = 16, //width of the initiator address bus
    parameter ITR_DAT_WIDTH   = 16,  //width of each initiator data bus
    parameter ITR_SEL_WIDTH   = 2,  //number of initiator write data select lines
    parameter TGA_WIDTH       = 1,  //number of propagated address tags
    parameter TGC_WIDTH       = 1,  //number of propagated cycle tags
    parameter TGRD_WIDTH      = 1,  //number of propagated read data tags
    parameter TGWD_WIDTH      = 1,  //number of propagated write data tags
    parameter BIG_ENDIAN      = 1)  //1=big endian, 0=little endian

   (//Clock and reset
    //---------------
    input wire                           clk_i,            //module clock
    input wire                           async_rst_i,      //asynchronous reset
    input wire                           sync_rst_i,       //synchronous reset

    //Initiator interface
    //-------------------
    input  wire                          itr_cyc_i,        //bus cycle indicator       +-
    input  wire                          itr_stb_i,        //access request            |
    input  wire                          itr_we_i,         //write enable              |
    input  wire                          itr_lock_i,       //uninterruptable bus cycle | initiator
    input  wire [ITR_SEL_WIDTH-1:0]      itr_sel_i,        //write data selects        | initiator
    input  wire [ITR_ADR_WIDTH-1:0]      itr_adr_i,        //address bus               | to
    input  wire [ITR_DAT_WIDTH-1:0]      itr_dat_i,        //write data bus            | target
    input  wire [TGA_WIDTH-1:0]          itr_tga_i,        //address tags              |
    input  wire [TGC_WIDTH-1:0]          itr_tgc_i,        //bus cycle tags            |
    input  wire [TGWD_WIDTH-1:0]         itr_tgd_i,        //write data tags           +-
    output reg                           itr_ack_o,        //bus cycle acknowledge     +-
    output reg                           itr_err_o,        //error indicator           | target
    output reg                           itr_rty_o,        //retry request             | to
    output reg                           itr_stall_o,      //access delay              | initiator
    output wire [ITR_DAT_WIDTH-1:0]      itr_dat_o,        //read data bus             |
    output wire [TGRD_WIDTH-1:0]         itr_tgd_o,        //read data tags            +-

    //Target interfaces
    //-----------------
    output wire                          tgt_cyc_o,        //bus cycle indicator       +-
    output wire                          tgt_stb_o,        //access request            |
    output wire                          tgt_we_o,         //write enable              |
    output reg                           tgt_lock_o,       //uninterruptable bus cycle |
    output wire [(ITR_SEL_WIDTH/2)-1:0]  tgt_sel_o,        //write data selects        | initiator
    output wire [ITR_ADR_WIDTH:0]        tgt_adr_o,        //write data selects        | to
    output wire [(ITR_DAT_WIDTH/2)-1:0]  tgt_dat_o,        //write data bus            | target
    output wire [TGA_WIDTH-1:0]          tgt_tga_o,        //address tags              |
    output wire [TGC_WIDTH-1:0]          tgt_tgc_o,        //bus cycle tags            |
    output wire [TGWD_WIDTH-1:0]         tgt_tgd_o,        //write data tags           +-
    input  wire                          tgt_ack_i,        //bus cycle acknowledge     +-
    input  wire                          tgt_err_i,        //error indicator           | target
    input  wire                          tgt_rty_i,        //retry request             | to
    input  wire                          tgt_stall_i,      //access delay              | initiator
    input  wire [(ITR_DAT_WIDTH/2)-1:0]  tgt_dat_i,        //read data bus             |
    input  wire [TGRD_WIDTH-1:0]         tgt_tgd_i);       //read data tags            +-

   //Internal signals
   reg  [1:0]                            state_next;                               //next state
   wire [(ITR_SEL_WIDTH/2)-1:0]          itr_sel_msd = itr_sel_i[ITR_SEL_WIDTH-1:(ITR_SEL_WIDTH/2)];
   wire [(ITR_SEL_WIDTH/2)-1:0]          itr_sel_lsd = itr_sel_i[(ITR_SEL_WIDTH/2)-1:0];
   reg                                   capture_dat;                              //capture read data
   reg                                   tgt_dat_msd;                              //drive MSD to target data bus
   reg                                   tgt_dat_lsd;                              //drive LSD to target data bus
   reg                                   tgt_adr_0;                                //LSB of target address
   reg                                   itr_dat_cap;                              //drive captured data to initiator

   //Internal registers
   reg  [1:0]                            state_reg;                                //state variable
   reg  [(ITR_DAT_WIDTH/2)-1:0]          tgt_dat_reg;                              //state variable

   //Signal propagation to the target bus
   assign tgt_cyc_o        = itr_cyc_i;                                            //bus cycle indicator       +-
   assign tgt_stb_o        = itr_stb_i;                                            //access request            |
   assign tgt_we_o         = itr_we_i;                                             //write enable              |
   assign tgt_sel_o        = tgt_dat_msd ? itr_sel_msd :                           //write data selects        |
                                           itr_sel_lsd;                            //                          | initiator
   assign tgt_adr_o        = {itr_adr_i, tgt_adr_0};                               //write data selects        | to
   assign tgt_dat_o        = (tgt_dat_msd) ?                                       //write data bus            | target
                               itr_dat_i[ITR_DAT_WIDTH-1:(ITR_DAT_WIDTH/2)] :      //                          |
                               itr_dat_i[(ITR_DAT_WIDTH/2)-1:0];                   //                          |
   assign tgt_tga_o        = itr_tga_i;                                            //address tags              |
   assign tgt_tgc_o        = itr_tgc_i;                                            //bus cycle tags            |
   assign tgt_tgd_o        = itr_tgd_i;                                            //write data tags           +-

   //Signal propagation to the initiator bus
   assign itr_dat_o[ITR_DAT_WIDTH-1:ITR_DAT_WIDTH/2] = itr_dat_cap ?               //read data bus             +-
                                                            tgt_dat_reg :          //                          | target to
                                                            tgt_dat_i;             //                          | initiator
   assign itr_dat_o[(ITR_DAT_WIDTH/2)-1:0]           = tgt_dat_i;                  //read data tags            +-

   //Capture read data
   always @(posedge async_rst_i or posedge clk_i)
     if (async_rst_i)                                                              //asynchronous reset
       tgt_dat_reg <= {ITR_DAT_WIDTH/2{1'b0}};
     else if (sync_rst_i)                                                          //synchronous reset
       tgt_dat_reg <= {ITR_DAT_WIDTH/2{1'b0}};
     else if (capture_dat)                                                         //capture read data
       tgt_dat_reg <= itr_dat_i[ITR_DAT_WIDTH-1:ITR_DAT_WIDTH/2];

   //Finite state machine
   parameter STATE_FIRST_STB  = 2'b00;                                             //first bus request (reset state)
   parameter STATE_FIRST_ACK  = 2'b01;                                             //first bus acknowledge
   parameter STATE_SECOND_STB = 2'b10;                                             //second bus request
   parameter STATE_SECOND_ACK = 2'b11;                                             //second bus acknowledge
   always @*
     begin
        //Default outputs
        state_next  = state_reg;                                                   //remain in current state
        tgt_lock_o  = &{|itr_sel_msd, |itr_sel_lsd} | itr_lock_i;                  //propagate cycle lock
        itr_ack_o   = tgt_ack_i;                                                   //propagate acknowledge
        itr_err_o   = tgt_err_i;                                                   //propagate error
        itr_rty_o   = tgt_rty_i;                                                   //propagate retry request
        itr_stall_o = tgt_stall_i;                                                 //propagate stalls
        capture_dat = 1'b0;                                                        //don't capture read data
        tgt_dat_msd =  |itr_sel_msd;                                               //drive MSD to target data bus
        tgt_dat_lsd = ~|itr_sel_msd;                                               //drive LSD to target data bus
        tgt_adr_0   = |itr_sel_msd ^ |BIG_ENDIAN;                                  //LSB of target address
        itr_dat_cap = 1'b0;                                                        //don't drive captured data to initiator

        case (state_reg)
          STATE_FIRST_STB:
            begin
               if (itr_cyc_i & itr_stb_i & ~tgt_stall_i)                           //new bus request
                 begin
                    state_next  = STATE_FIRST_ACK;                                 //plain bus access
                    itr_stall_o = &{|itr_sel_msd, |itr_sel_lsd} | tgt_stall_i;     //propagate stalls
                 end
            end
          STATE_FIRST_ACK:
            begin
               if (|{tgt_err_i, tgt_rty_i})                                        //error response
                 begin
                    if (itr_cyc_i & itr_stb_i & ~tgt_stall_i)                      //new bus request
                      itr_stall_o = &{|itr_sel_msd, |itr_sel_lsd} | tgt_stall_i;   //propagate stalls
                    else
                      state_next = STATE_FIRST_STB;                                //bus is idle
                 end
               else if (tgt_ack_i)                                                 //bus acknowledge
                 if (~&{|itr_sel_msd, |itr_sel_lsd})                               //acknowledge of single access
                   begin
                      if (itr_cyc_i & itr_stb_i & ~tgt_stall_i)                    //new bus request
                        itr_stall_o = &{|itr_sel_msd, |itr_sel_lsd} | tgt_stall_i; //propagate stalls
                      else
                        state_next  = STATE_FIRST_STB;                             //bus is igle
                   end
                 else                                                              //acknowledge of split access
                   begin
                    state_next  = tgt_stall_i ? STATE_SECOND_STB :                 //wait while stalled
                                                STATE_SECOND_ACK;                  //wait for ack
                    itr_ack_o   = 1'b0;                                            //don't acknowledge
                    itr_stall_o = 1'b1;                                            //stall initiator
                    capture_dat = 1'b1;                                            //capture read data
                    tgt_dat_msd = 1'b0;                                            //don't drive MSD to target data bus
                    tgt_dat_lsd = 1'b1;                                            //drive LSD to target data bus
                    tgt_adr_0   = |BIG_ENDIAN;                                     //drive LSD address
                 end // else: !if(~&{|itr_sel_msd, |itr_sel_lsd})
            end // case: STATE_FIRST_ACK
          STATE_SECOND_STB:
            begin
               state_next  = tgt_stall_i ? state_reg :                             //wait while stalled
                                           STATE_SECOND_ACK;                       //wait for ack
               itr_ack_o   = 1'b0;                                                 //don't acknowledge
               itr_err_o   = 1'b0;                                                 //don't flag error
               itr_rty_o   = 1'b0;                                                 //don't request retry
               itr_stall_o = 1'b1;                                                 //stall initiator
               capture_dat = 1'b1;                                                 //capture read data
               tgt_dat_msd = 1'b0;                                                 //don't drive MSD to target data bus
               tgt_dat_lsd = 1'b1;                                                 //drive LSD to target data bus
               tgt_adr_0   = |BIG_ENDIAN;                                          //drive LSD address
               itr_dat_cap = 1'b1;                                                 //drive captured data to initiator
            end // case: STATE_SECOND_STB
          STATE_SECOND_ACK:
            begin
               itr_dat_cap = 1'b1;                                                 //drive captured data to initiator
               if (|{tgt_ack_i, tgt_err_i, tgt_rty_i})                             //acknowledge or error
                 begin
                    if (itr_cyc_i & itr_stb_i & ~tgt_stall_i)                      //new bus request
                      begin
                         state_next  = STATE_FIRST_ACK;                            //plain bus access
                         itr_stall_o = &{|itr_sel_msd, |itr_sel_lsd} | tgt_stall_i;//propagate stalls
                      end
                    else
                      state_next  = STATE_FIRST_STB;                               //plain bus access
                 end
            end // case: STATE_SECOND_ACK
        endcase // case (state_reg)
     end // always @ *

   //State variable
   always @(posedge async_rst_i or posedge clk_i)
     if (async_rst_i)                                                              //asynchronous reset
       state_reg <= STATE_FIRST_STB;
     else if (sync_rst_i)                                                          //synchronous reset
       state_reg <= STATE_FIRST_STB;
     else if(1)
       state_reg <= state_next;                                                    //state transition

endmodule // WbXbc_reducer
