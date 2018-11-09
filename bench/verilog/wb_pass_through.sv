//###############################################################################
//# WbXbc - Wishbone Access Pass-Through Assertions (Pipelined)                 #
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
//#    This set of assertion monitors a pipelined Wishbone initiator for        #
//#    protocol violations.                                                     #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   October 12, 2018                                                          #
//#      - Initial release                                                      #
//#   November 9, 2018                                                          #
//#      - Disableing assertions and constraints in reset                       #
//#      - Added status signals to constraint FSM states                        #
//###############################################################################
`default_nettype none

module wb_pass_through
  #(parameter ADR_WIDTH   = 16,                              //width of the address bus
    parameter DAT_WIDTH   = 16,                              //width of each data bus
    parameter SEL_WIDTH   = 2,                               //number of data select lines
    parameter TGA_WIDTH   = 1,                               //number of address tags
    parameter TGC_WIDTH   = 1,                               //number of cycle tags
    parameter TGRD_WIDTH  = 1,                               //number of read data tags
    parameter TGWD_WIDTH  = 1)                               //number of write data tags

   (//Assertion control
    //-----------------
    input wire                  pass_through_en,             //module clock

    //Clock and reset
    //---------------
    input wire                  clk_i,                       //module clock
    input wire                  async_rst_i,                 //asynchronous reset
    input wire                  sync_rst_i,                  //synchronous reset

    //Initiator interface
    //-------------------
    input wire                  itr_cyc_i,                   //bus cycle indicator       +-
    input wire                  itr_stb_i,                   //access request            |
    input wire                  itr_we_i,                    //write enable              |
    input wire                  itr_lock_i,                  //uninterruptable bus cycle |
    input wire [SEL_WIDTH-1:0]  itr_sel_i,                   //write data selects        | initiator
    input wire [ADR_WIDTH-1:0]  itr_adr_i,                   //address bus               | to
    input wire [DAT_WIDTH-1:0]  itr_dat_i,                   //write data bus            | target
    input wire [TGA_WIDTH-1:0]  itr_tga_i,                   //address tags              |
    input wire [TGC_WIDTH-1:0]  itr_tgc_i,                   //bus cycle tags            |
    input wire [TGWD_WIDTH-1:0] itr_tgd_i,                   //write data tags           +-
    input wire                  itr_ack_o,                   //bus cycle acknowledge     +-
    input wire                  itr_err_o,                   //error indicator           | target
    input wire                  itr_rty_o,                   //retry request             | to
    input wire                  itr_stall_o,                 //access delay              | initiator
    input wire [DAT_WIDTH-1:0]  itr_dat_o,                   //read data bus             |
    input wire [TGRD_WIDTH-1:0] itr_tgd_o,                   //read data tags            +-

    //Target interfaces
    //-----------------
    input wire                  tgt_cyc_o,                   //bus cycle indicator       +-
    input wire                  tgt_stb_o,                   //access request            |
    input wire                  tgt_we_o,                    //write enable              |
    input wire                  tgt_lock_o,                  //uninterruptable bus cycle | initiator
    input wire [SEL_WIDTH-1:0]  tgt_sel_o,                   //write data selects        | to
    input wire [ADR_WIDTH-1:0]  tgt_adr_o,                   //address bus               | target
    input wire [DAT_WIDTH-1:0]  tgt_dat_o,                   //write data bus            |
    input wire [TGA_WIDTH-1:0]  tgt_tga_o,                   //propagated address tags   |
    input wire [TGC_WIDTH-1:0]  tgt_tgc_o,                   //bus cycle tags            |
    input wire [TGWD_WIDTH-1:0] tgt_tgd_o,                   //write data tags           +-
    input wire                  tgt_ack_i,                   //bus cycle acknowledge     +-
    input wire                  tgt_err_i,                   //error indicator           | target
    input wire                  tgt_rty_i,                   //retry request             | to
    input wire                  tgt_stall_i,                 //access delay              | initiator
    input wire [DAT_WIDTH-1:0]  tgt_dat_i,                   //read data bus             |
    input wire [TGRD_WIDTH-1:0] tgt_tgd_i,                   //read data tags            +-

    //Testbench status signals
    //------------------------
    output wire                 tb_fsm_reset,                //FSM in RESET state
    output wire                 tb_fsm_idle,                 //FSM in IDLE state
    output wire                 tb_fsm_busy);                //FSM in READ or WRITE state

   //Abbreviations
   wire                                    rst  = |{async_rst_i, sync_rst_i};           //reset
   wire                                    req  = &{~itr_stall_o, itr_cyc_i, itr_stb_i, //request
                                                     pass_through_en};                  //monitor enable
   wire                                    wreq = &{itr_we_i, req};                     //write request
   wire                                    rreq = &{itr_we_i, req};                     //read request
   wire                                    ack  = |{itr_ack_o, itr_err_o, itr_rty_o};   //acknowledge

   //State Machine
   //=============
   //                             wreq          _______
   //                     +------------------->/       \
   //                     |                    | WRITE |
   //                     |  +-----------------\_______/
   //                     |  | ~req & ack        ^  |
   //        _______     _|__v_                  |  |
   // rst   /       \   /      \             wreq|  |rreq
   //  O--->| RESET |-->| IDLE |               & |  | &
   //       \_______/   \______/              ack|  |ack
   //                     ^  |                   |  |
   //                     |  |    rreq          _|__v_
   //                     |  +---------------->/      \
   //                     |                    | READ |
   //                     +--------------------\______/
   //                          ~req & ack
   //State encoding
   parameter STATE_RESET = 2'b00;
   parameter STATE_IDLE  = 2'b01;
   parameter STATE_READ  = 2'b10;
   parameter STATE_WRITE = 2'b11;
   //State variable
   reg          [1:0]                           state_reg;
   reg          [1:0]                           state_next;
   always @(posedge async_rst_i or posedge clk_i)
     if (async_rst_i)                                        //asynchronous reset
       state_reg <= STATE_RESET;
     else if (sync_rst_i)                                    //synchronous reset
       state_reg <= STATE_RESET;
     else
       state_reg <= state_next;                              //state transition
   //State transitions
   always @*
     begin
        //Default transition
        state_next = state_reg; //remain in current state
        case (state_reg)
          STATE_RESET:
            begin
               state_next = STATE_IDLE;
            end
          STATE_IDLE:
            begin
               if (wreq)
                 state_next = STATE_WRITE;
               if (rreq)
                 state_next = STATE_READ;
            end
          STATE_WRITE:
            begin
               if (~req & ack)
                 state_next = STATE_IDLE;
               if (rreq & ack)
                 state_next = STATE_READ;
            end
          STATE_READ:
            begin
               if (~req & ack)
                 state_next = STATE_IDLE;
               if (wreq & ack)
                 state_next = STATE_WRITE;
            end
        endcase // case (state_reg)
     end // always @ *

   //Pass-through rules
   //==================
   always @(posedge clk_i)
   //always @($global_clock)
     if (~rst) //disable assertions and constraints in reset
       begin
          //Pass through bus request
          if ((state_reg == STATE_IDLE)  ||
              (state_reg == STATE_WRITE) ||
              (state_reg == STATE_READ))
            begin
               if (pass_through_en)
                 begin
                    assert (tgt_cyc_o   == itr_cyc_i);   //bus cycle indicator
                    assert (tgt_stb_o   == itr_stb_i);   //access request
                    assert (itr_stall_o == tgt_stall_i); //access delay
                 end // if (pass_through_en)
               if (req)
                 begin
                    assert (tgt_we_o   == itr_we_i);     //write enable
                    assert (tgt_lock_o == itr_lock_i);   //uninterruptable bus cycle
                    assert (tgt_sel_o  == itr_sel_i);    //data selects
                    assert (tgt_adr_o  == itr_adr_i);    //address bus
                    assert (tgt_tga_o  == itr_tga_i);    //address tags
                    assert (tgt_tgc_o  == itr_tgc_i);    //bus cycle tags
                 end // if (req)
               if (wreq)
                 begin
                    assert (tgt_dat_o  == itr_dat_i);    //write data bus
                    assert (tgt_tgd_o  == itr_tgd_i);    //write data tags
                 end // if (wreq)
            end // if ((state_reg == STATE_IDLE)  ||...

          //Pass through termination response
          if ((state_reg == STATE_WRITE) ||
              (state_reg == STATE_READ))
            begin
               assert (itr_ack_o == tgt_ack_i);          //bus cycle acknowledge
               assert (itr_err_o == tgt_err_i);          //error indicator
               assert (itr_rty_o == tgt_rty_i);          //retry request
            end // if ((state_reg == STATE_WRITE) ||...

          //Pass through read data
          if (state_reg == STATE_READ)
            begin
               assert (itr_dat_o == tgt_dat_i);          //read data bus
               assert (itr_tgd_o == tgt_tgd_i);          //read data tags
            end // if (state_reg == STATE_READ)
       end // if (~rst)

   //Testbench status signals
   //==================
   assign tb_fsm_reset =  (state_reg === STATE_RESET)  ? 1'b1 : 1'b0;
   assign tb_fsm_idle  =  (state_reg === STATE_IDLE)   ? 1'b1 : 1'b0;
   assign tb_fsm_busy  = ((state_reg === STATE_READ) ||
                          (state_reg === STATE_WRITE)) ? 1'b1 : 1'b0;

endmodule // wb_pass_through
