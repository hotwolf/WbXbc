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
//#    along with Ninq1.  If not, see <http://www.gnu.org/licenses/>.           #
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
//###############################################################################
`default_nettype none

module WbXbc_arbiter
  #(parameter ITR_CNT     = 4,   //number of initiator busses
    parameter ADDR_WIDTH  = 16,  //width of the address bus
    parameter DATA_WIDTH  = 16,  //width of each data bus
    parameter SEL_WIDTH   = 2,   //number of write data select lines
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
    input  wire [(ITR_CNT*ADDR_WIDTH)-1:0] itr_adr_i,        //address bus               | to
    input  wire [(ITR_CNT*DATA_WIDTH)-1:0] itr_dat_i,        //write data bus            | target
    input  wire [ITR_CNT-1:0]              itr_tga_prio_i,   //access priorities         |
    input  wire [(ITR_CNT*TGA_WIDTH)-1:0]  itr_tga_i,        //generic address tags      |
    input  wire [(ITR_CNT*TGC_WIDTH)-1:0]  itr_tgc_i,        //bus cycle tags            |
    input  wire [(ITR_CNT*TGWD_WIDTH)-1:0] itr_tgd_i,        //write data tags           +-
    output wire [ITR_CNT-1:0]              itr_ack_o,        //bus cycle acknowledge     +-
    output wire [ITR_CNT-1:0]              itr_err_o,        //error indicator           | target
    output wire [ITR_CNT-1:0]              itr_rty_o,        //retry request             | to
    output reg  [ITR_CNT-1:0]              itr_stall_o,      //access delay              | initiator
    output wire [(ITR_CNT*DATA_WIDTH)-1:0] itr_dat_o,        //read data bus             |
    output wire [(ITR_CNT*TGRD_WIDTH)-1:0] itr_tgd_o,        //read data tags            +-

    //Target interfaces
    //-----------------
    output wire                            tgt_cyc_o,        //bus cycle indicator       +-
    output reg                             tgt_stb_o,        //access request            |
    output wire                            tgt_we_o,         //write enable              |
    output wire                            tgt_lock_o,       //uninterruptable bus cycle | initiator
    output reg  [SEL_WIDTH-1:0]            tgt_sel_o,        //write data selects        | to
    output reg  [ADDR_WIDTH-1:0]           tgt_adr_o,        //address bus               | target
    output reg  [DATA_WIDTH-1:0]           tgt_dat_o,        //write data bus            |
    output reg  [TGA_WIDTH-1:0]            tgt_tga_o,        //propagated address tags   |
    output reg  [TGC_WIDTH-1:0]            tgt_tgc_o,        //bus cycle tags            |
    output reg  [TGWD_WIDTH-1:0]           tgt_tgd_o,        //write data tags           +-
    input  wire                            tgt_ack_i,        //bus cycle acknowledge     +-
    input  wire                            tgt_err_i,        //error indicator           | target
    input  wire                            tgt_rty_i,        //retry request             | to
    input  wire                            tgt_stall_i,      //access delay              | initiator
    input  wire [DATA_WIDTH-1:0]           tgt_dat_i,        //read data bus             |
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
   //always @(hiprio_req or loprio_req or arb_req)
     begin
        arb_req = {ITR_CNT{1'b0}};
        for (i=0; i<ITR_CNT; i=i+1)                   //high priority requests
          if (~|arb_req)
            arb_req[i] = hiprio_req[i];               //low priority requests
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
   assign tgt_cyc_o   = |(cyc_sel & itr_cyc_i);           //bus cycle indicator
   assign tgt_we_o    = |(cyc_sel & itr_we_i);            //write enable
   assign tgt_lock_o  = |(cyc_sel & itr_lock_i);          //write enable

   always @*                                              //write data selects
   //always @(cyc_sel or itr_sel_i)                       //write data selects
     begin
        tgt_sel_o = {SEL_WIDTH{1'b0}};
        for (k=0; k<(ITR_CNT*SEL_WIDTH); k=k+1)
          tgt_sel_o[k%SEL_WIDTH] = tgt_sel_o[k%SEL_WIDTH] |
                                   (cyc_sel[k/SEL_WIDTH] & itr_sel_i[k]);
     end

   always @*                                              //address bus
   //always @(cyc_sel or itr_adr_i)                       //address bus
     begin
        tgt_adr_o = {ADDR_WIDTH{1'b0}};
        for (l=0; l<(ITR_CNT*ADDR_WIDTH); l=l+1)
          tgt_adr_o[l%ADDR_WIDTH] = tgt_adr_o[l%ADDR_WIDTH] |
                                    (cyc_sel[l/ADDR_WIDTH] & itr_adr_i[l]);
     end

   always @*                                              //address tags
   //always @(cyc_sel or itr_tga_i)                       //address tags
     begin
        tgt_tga_o = {TGA_WIDTH{1'b0}};
        for (m=0; m<(ITR_CNT*TGA_WIDTH); m=m+1)
          tgt_tga_o[m%TGA_WIDTH] = tgt_tga_o[m%TGA_WIDTH] |
                                   (cyc_sel[m/TGA_WIDTH] & itr_tga_i[m]);
     end

   always @*                                              //bus cycle tags
   //always @(cyc_sel or itr_tgc_i)                       //bus cycle tags
     begin
        tgt_tgc_o = {TGC_WIDTH{1'b0}};
        for (n=0; n<(ITR_CNT*TGC_WIDTH); n=n+1)
          tgt_tgc_o[n%TGC_WIDTH] = tgt_tgc_o[n%TGC_WIDTH] |
                                   (cyc_sel[n/TGC_WIDTH] & itr_tgc_i[n]);
     end

   always @*                                              //write data bus
   //always @(cur_itr_reg or itr_dat_i)                   //write data bus
     begin
        tgt_dat_o = {DATA_WIDTH{1'b0}};
        for (o=0; o<(ITR_CNT*DATA_WIDTH); o=o+1)
          tgt_dat_o[o%DATA_WIDTH] = tgt_dat_o[o%DATA_WIDTH] |
                                    (cur_itr_reg[o/DATA_WIDTH] & itr_dat_i[o]);
     end

   always @*                                              //write data tags
   //always @(cur_itr_reg or itr_tgd_i)                   //write data tags
     begin
        tgt_tgd_o = {TGWD_WIDTH{1'b0}};
        for (p=0; p<(ITR_CNT*TGWD_WIDTH); p=p+1)
          tgt_tgd_o[p%TGWD_WIDTH] = tgt_tgd_o[p%TGWD_WIDTH] |
                                    (cur_itr_reg[p/TGWD_WIDTH] & itr_tgd_i[p]);
     end

   //Finite state machine
   parameter STATE_READY       = 1'b0;  //awaiting bus request (reset state)
   parameter STATE_ACK_PENDING = 1'b1;  //awaiting bus acknowledge
   always @*
   //always @(state_reg      or //state variable
   //         tgt_stall_i    or //access delay
   //         arb_req        or //arbitrated request (one hot)
   //         cyc_sel        or //select the initiator for the current
   //         cur_itr_reg    or //current initiator bus (one hot)
   //         any_req        or //any access request at all
   //         any_ack        or //any acknowledge request at all
   //         locked)           //atomic access sequence
     begin
        //Default outputs
        state_next  = state_reg;                                      //remain in current state
        tgt_stb_o   = 1'b0;                                           //no target bus request
        itr_stall_o = {ITR_CNT{tgt_stall_i}};                         //propagate stall from target
        cyc_sel     = arb_req;                                        //propagate signals of arbitrated initiator
        capture_req = 1'b0;                                           //don't capture arbitrated request
        case (state_reg)
          STATE_READY:
            begin
               if (any_req & ~tgt_stall_i & ~locked)                  //new bus request, no stall, not locked
                 begin
                    state_next  = STATE_ACK_PENDING;                  //wait for acknowledge
                    tgt_stb_o   = 1'b1;                               //request target bus
                    itr_stall_o = ~arb_req;                           //stall all other initiators
                    cyc_sel     =  arb_req;                           //propagate signals of arbitrated initiator
                    capture_req = 1'b1;                               //capture arbitrated request
                 end
               else
               if (any_req & ~tgt_stall_i &  locked)                  //new bus request, no stall, locked
                 begin
                    state_next  = STATE_ACK_PENDING;                  //wait for acknowledge
                    tgt_stb_o   = 1'b1;                               //request target bus
                    itr_stall_o = ~cur_itr_reg;                       //stall all other initiators
                    cyc_sel     =  cur_itr_reg;                       //propagate signals of arbitrated initiator
                 end
            end // case: STATE_READY
          STATE_ACK_PENDING:
            begin
               if (tgt_ack_i)                                         //request acknowleged
                 if ( any_req & ~tgt_stall_i & ~locked)               //new bus request, no stall, not locked
                   begin
                      tgt_stb_o   = 1'b1;                             //request target bus
                      itr_stall_o = ~cyc_sel;                         //stall all other initiators
                      cyc_sel     =  arb_req;                         //propagate signals of arbitrated initiator
                      capture_req = 1'b1;                             //capture arbitrated request
                   end
                 else
                 if ( any_req & ~tgt_stall_i &  locked)               //new bus request, no stall, locked
                   begin
                      tgt_stb_o   = 1'b1;                             //request target bus
                      itr_stall_o = ~cur_itr_reg;                     //stall all other initiators
                      cyc_sel     =  cur_itr_reg;                     //propagate signals of arbitrated initiator
                   end
                 else
                   begin
                      state_next  = STATE_READY;                      //remain in current state
                   end // else: !if( any_req & ~tgt_stall_i)
               else
                 begin
                    itr_stall_o = ~cyc_sel;                           //stall all other initiators
                    cyc_sel     =  cur_itr_reg;                       //propagate signals of captured initiator
                 end // else: !if( any_req & ~tgt_stall_i)
            end // case: STATE_ACK_PENDING
          //default:
          //  begin
          //     state_next = STATE_READY;                            //catch runawy state machine
          //  end
        endcase // case (state_reg)
     end // always @ (state            or...

   //State variable
   always @(posedge async_rst_i or posedge clk_i)
     if (async_rst_i)                                                 //asynchronous reset
       state_reg <= STATE_READY;
     else if (sync_rst_i)                                             //synchronous reset
       state_reg <= STATE_READY;
     else if(1)
       state_reg <= state_next;                                       //state transition

endmodule // WbXbc_arbiter
