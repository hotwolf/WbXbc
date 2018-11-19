//###############################################################################
//# WbXbc - Wishbone Crossbar Components - Bus Arbiter                          #
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
//#    This module implements a bus arbiter for the pipelined Wishbone          #
//#    protocol. Accesses from multiple initiator busses are arbitrated and     #
//#    propagated to the target bus. Each initiator bus can request bus         #
//#    accesses at two priority levels. The priority levels are selected via a  #
//#    set of address tags. Access requests of equal priority are arbitrated    #
//#    with a fixed priority (initiator 0 has the higheest priority).           #
//#                                                                             #
//#                           +-------------------+                             #
//#                       --->|                   |                             #
//#                           |                   |                             #
//#              multiple --->|       WbXbc       |       one                   #
//#             initiator     |      arbiter      |---> target                  #
//#               busses   ...|                   |       bus                   #
//#                           |                   |                             #
//#                       --->|                   |                             #
//#                           +-------------------+                             #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   July 18, 2018                                                             #
//#      - Initial release                                                      #
//#   October 8, 2018                                                           #
//#      - Updated parameter and signal naming                                  #
//###############################################################################
`default_nettype none

module WbXbc_arbiter
  #(parameter ITR_CNT     = 4,   //number of initiator busses
    parameter ADR_WIDTH   = 16,  //width of the address bus
    parameter DAT_WIDTH   = 16,  //width of each data bus
    parameter SEL_WIDTH   = 2,   //number of data select lines
    parameter TGA_WIDTH   = 1,   //number of propagated address tags
    parameter TGC_WIDTH   = 1,   //number of propagated cycle tags
    parameter TGRD_WIDTH  = 1,   //number of propagated read data tags
    parameter TGWD_WIDTH  = 1)   //number of propagated write data tags

   (//Clock and reset
    //---------------
    input wire                             clk_i,            //module clock
    input wire                             async_rst_i,      //asynchronous reset
    input wire                             sync_rst_i,       //synchronous reset

    //Initiator interface
    //-------------------
    input  wire [ITR_CNT-1:0]              itr_cyc_i,        //bus cycle indicator       +-
    input  wire [ITR_CNT-1:0]              itr_stb_i,        //access request            |
    input  wire [ITR_CNT-1:0]              itr_we_i,         //write enable              |
    input  wire [ITR_CNT-1:0]              itr_lock_i,       //uninterruptable bus cycle |
    input  wire [(ITR_CNT*SEL_WIDTH)-1:0]  itr_sel_i,        //write data selects        | initiator
    input  wire [(ITR_CNT*ADR_WIDTH)-1:0]  itr_adr_i,        //address bus               | to
    input  wire [(ITR_CNT*DAT_WIDTH)-1:0]  itr_dat_i,        //write data bus            | target
    input  wire [(ITR_CNT*TGA_WIDTH)-1:0]  itr_tga_i,        //generic address tags      |
    input  wire [ITR_CNT-1:0]              itr_tga_prio_i,   //access priorities         |
    input  wire [(ITR_CNT*TGC_WIDTH)-1:0]  itr_tgc_i,        //bus cycle tags            |
    input  wire [(ITR_CNT*TGWD_WIDTH)-1:0] itr_tgd_i,        //write data tags           +-
    output wire [ITR_CNT-1:0]              itr_ack_o,        //bus cycle acknowledge     +-
    output wire [ITR_CNT-1:0]              itr_err_o,        //error indicator           | target
    output wire [ITR_CNT-1:0]              itr_rty_o,        //retry request             | to
    output reg  [ITR_CNT-1:0]              itr_stall_o,      //access delay              | initiator
    output wire [(ITR_CNT*DAT_WIDTH)-1:0]  itr_dat_o,        //read data bus             |
    output wire [(ITR_CNT*TGRD_WIDTH)-1:0] itr_tgd_o,        //read data tags            +-

    //Target interfaces
    //-----------------
    output reg                             tgt_cyc_o,        //bus cycle indicator       +-
    output reg                             tgt_stb_o,        //access request            |
    output wire                            tgt_we_o,         //write enable              |
    output wire                            tgt_lock_o,       //uninterruptable bus cycle | initiator
    output reg  [SEL_WIDTH-1:0]            tgt_sel_o,        //write data selects        | to
    output reg  [ADR_WIDTH-1:0]            tgt_adr_o,        //address bus               | target
    output reg  [DAT_WIDTH-1:0]            tgt_dat_o,        //write data bus            |
    output reg  [TGA_WIDTH-1:0]            tgt_tga_o,        //propagated address tags   |
    output reg  [TGC_WIDTH-1:0]            tgt_tgc_o,        //bus cycle tags            |
    output reg  [TGWD_WIDTH-1:0]           tgt_tgd_o,        //write data tags           +-
    input  wire                            tgt_ack_i,        //bus cycle acknowledge     +-
    input  wire                            tgt_err_i,        //error indicator           | target
    input  wire                            tgt_rty_i,        //retry request             | to
    input  wire                            tgt_stall_i,      //access delay              | initiator
    input  wire [DAT_WIDTH-1:0]            tgt_dat_i,        //read data bus             |
    input  wire [TGRD_WIDTH-1:0]           tgt_tgd_i);       //read data tags            +-

   //Internal signals
   wire [ITR_CNT-1:0] hiprio_req  =  itr_tga_prio_i & itr_cyc_i & itr_stb_i; //high priority requests
   wire [ITR_CNT-1:0] loprio_req  = ~itr_tga_prio_i & itr_cyc_i & itr_stb_i; //low  priority requests
   reg  [ITR_CNT-1:0] arb_req;                                               //arbitrated request (one hot)
   reg  [ITR_CNT-1:0] cyc_sel;                                               //select the initiator for the current bus cycle
   wire               any_req     = |(itr_cyc_i & itr_stb_i);                //any access request at all
   wire               any_ack     = |{tgt_ack_i, tgt_err_i, tgt_rty_i};      //any acknowledge request at all
   wire               locked      = |(itr_cyc_i & itr_stb_i &                //atomic access sequence
                                      itr_lock_i & cur_itr_reg);
   reg                capture_req;                                           //capture arbitrated request
   reg                state_next;                                            //next state

   //Internal registers
   reg  [ITR_CNT-1:0] cur_itr_reg;                                           //current initiator bus (one hot)
   reg                state_reg;                                             //state variable

   //Counters
   integer            i, j, k, l, m, n, o, p;

   //Arbitrate incoming requests
   always @*
     begin
        arb_req = {ITR_CNT{1'b0}};
        for (i=0; i<ITR_CNT; i=i+1)                       //high priority requests
          if (~|arb_req)
            arb_req[i] = hiprio_req[i];                   //low priority requests
        for (j=0; j<ITR_CNT; j=j+1)
          if (~|arb_req)
            arb_req[j] = loprio_req[j];
     end

   //Captured request
   always @(posedge async_rst_i or posedge clk_i)
     if(async_rst_i)                                      //asynchronous reset
       cur_itr_reg <= {ITR_CNT{1'b0}};                    //reset initiator selector
     else if(sync_rst_i)                                  //synchronous reset
       cur_itr_reg <= {ITR_CNT{1'b0}};                    //reset initiator selector
     else if (capture_req)
       cur_itr_reg <= arb_req;                            //capture next iterator selector

   //Plain signal propagation to the initiator bus
   assign itr_dat_o = {ITR_CNT{tgt_dat_i}};               //read data busses
   assign itr_tgd_o = {ITR_CNT{tgt_tgd_i}};               //read data tags

   //Multiplexed signal propagation to the initiator bus
   assign itr_ack_o = {ITR_CNT{tgt_ack_i}} & cur_itr_reg; //bus cycle acknowledge
   assign itr_err_o = {ITR_CNT{tgt_err_i}} & cur_itr_reg; //error indicator
   assign itr_rty_o = {ITR_CNT{tgt_rty_i}} & cur_itr_reg; //retry request

   //Multiplexed signal propagation to the target bus
   assign tgt_we_o    = |(cyc_sel & itr_we_i);            //write enable
   assign tgt_lock_o  = |(cyc_sel & itr_lock_i);          //write enable

   always @*                                              //write data selects
     begin
        tgt_sel_o = {SEL_WIDTH{1'b0}};
        for (k=0; k<(ITR_CNT*SEL_WIDTH); k=k+1)
          tgt_sel_o[k%SEL_WIDTH] = tgt_sel_o[k%SEL_WIDTH] |
                                   (cyc_sel[k/SEL_WIDTH] & itr_sel_i[k]);
     end

   always @*                                              //address bus
     begin
        tgt_adr_o = {ADR_WIDTH{1'b0}};
        for (l=0; l<(ITR_CNT*ADR_WIDTH); l=l+1)
          tgt_adr_o[l%ADR_WIDTH] = tgt_adr_o[l%ADR_WIDTH] |
                                    (cyc_sel[l/ADR_WIDTH] & itr_adr_i[l]);
     end

   always @*                                              //address tags
     begin
        tgt_tga_o = {TGA_WIDTH{1'b0}};
        for (m=0; m<(ITR_CNT*TGA_WIDTH); m=m+1)
          tgt_tga_o[m%TGA_WIDTH] = tgt_tga_o[m%TGA_WIDTH] |
                                   (cyc_sel[m/TGA_WIDTH] & itr_tga_i[m]);
     end

   always @*                                              //bus cycle tags
     begin
        tgt_tgc_o = {TGC_WIDTH{1'b0}};
        for (n=0; n<(ITR_CNT*TGC_WIDTH); n=n+1)
          tgt_tgc_o[n%TGC_WIDTH] = tgt_tgc_o[n%TGC_WIDTH] |
                                   (cyc_sel[n/TGC_WIDTH] & itr_tgc_i[n]);
     end

   always @*                                              //write data bus
     begin
        tgt_dat_o = {DAT_WIDTH{1'b0}};
        for (o=0; o<(ITR_CNT*DAT_WIDTH); o=o+1)
          tgt_dat_o[o%DAT_WIDTH] = tgt_dat_o[o%DAT_WIDTH] |
                                    (cyc_sel[o/DAT_WIDTH] & itr_dat_i[o]);
     end

   always @*                                              //write data tags
     begin
        tgt_tgd_o = {TGWD_WIDTH{1'b0}};
        for (p=0; p<(ITR_CNT*TGWD_WIDTH); p=p+1)
          tgt_tgd_o[p%TGWD_WIDTH] = tgt_tgd_o[p%TGWD_WIDTH] |
                                    (cyc_sel[p/TGWD_WIDTH] & itr_tgd_i[p]);
     end

   //Finite state machine
   parameter STATE_IDLE       = 1'b0;  //awaiting bus request (reset state)
   parameter STATE_BUSY       = 1'b1;  //awaiting bus acknowledge
   always @*
     begin
        //Default outputs
        state_next  = state_reg;                                      //remain in current state
        tgt_cyc_o   = 1'b0;                                           //target bus idle
        tgt_stb_o   = 1'b0;                                           //no target bus request
        itr_stall_o = {ITR_CNT{tgt_stall_i}};                         //propagate stall from target
        cyc_sel     = arb_req;                                        //propagate signals of arbitrated initiator
        capture_req = 1'b0;                                           //don't capture arbitrated request
        case (state_reg)
          STATE_IDLE:
            begin
               if (any_req)                                           //new bus request
                 begin
                    tgt_cyc_o   = 1'b1;                               //signal bus activity
                    tgt_stb_o   = 1'b1;                               //propagate new bus request
                 end
               if (any_req & ~tgt_stall_i)                            //new bus request, no stall
                 begin
                    state_next  = STATE_BUSY;                         //wait for acknowledge
                 end
               if (any_req & ~tgt_stall_i & ~locked)                  //new bus request, no stall, not locked
                 begin
                    itr_stall_o = ~arb_req;                           //stall all other initiators
                    capture_req = 1'b1;                               //capture arbitrated request
                 end
               if (any_req & ~tgt_stall_i & locked)                   //new bus request, no stall, locked
                 begin
                    itr_stall_o = ~cur_itr_reg;                       //stall all other initiators
                    cyc_sel     =  cur_itr_reg;                       //propagate signals of arbitrated initiator
                 end
            end // case: STATE_IDLE
          STATE_BUSY:
            begin
               tgt_cyc_o   = 1'b1;                                    //signal bus activity
               if (any_ack & any_req & ~tgt_stall_i)                  //request acknowleged, new bus request, no stall
                 begin
                    tgt_stb_o   = 1'b1;                               //request target bus
                 end
               if (any_ack & any_req & ~tgt_stall_i & ~locked)       //request acknowleged, new bus request, no stall, not locked
                 begin
                    itr_stall_o = ~cyc_sel;                          //stall all other initiators
                    cyc_sel     =  arb_req;                          //propagate signals of arbitrated initiator
                    capture_req = 1'b1;                              //capture arbitrated request
                 end
               if (any_ack & any_req & ~tgt_stall_i & locked)       //request acknowleged, new bus request, no stall, locked
                 begin
                    itr_stall_o = ~cur_itr_reg;                     //stall all other initiators
                    cyc_sel     =  cur_itr_reg;                     //propagate signals of arbitrated initiator
                 end
               if (any_ack & (~any_req | tgt_stall_i))              //request acknowleged, no bus request or stall
                 begin
                    state_next  = STATE_IDLE;                       //go to idle state
                 end
               if (~any_ack)                                          //no acknowlege
                 begin
                    itr_stall_o = ~cur_itr_reg;                       //stall all other initiators
                    cyc_sel     =  cur_itr_reg;                       //propagate signals of captured initiator
                 end
            end // case: STATE_BUSY
        endcase // case (state_reg)
     end // always @ (state            or...

   //State variable
   always @(posedge async_rst_i or posedge clk_i)
     if (async_rst_i)                                                 //asynchronous reset
       state_reg <= STATE_IDLE;
     else if (sync_rst_i)                                             //synchronous reset
       state_reg <= STATE_IDLE;
     else if(1)
       state_reg <= state_next;                                       //state transition

endmodule // WbXbc_arbiter
