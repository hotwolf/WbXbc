//###############################################################################
//# WbXbc - Wishbone Crossbar Components - Plain Crossbar Switch                #
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
//#    This module implements a full crossbar switch between a set of initator  #
//#    busses and a set of target busses, all using the pipelined Wishbone      #
//#    protocol.                                                                #
//#                                                                             #
//#                           +-------------------+                             #
//#               address --->|                   |                             #
//#               regions     |                   |                             #
//#                           |                   |                             #
//#                       --->|                   |--->                         #
//#                           |       WbXbc       |                             #
//#              multiple --->|       xbar        |--->  multiple               #
//#             initiator     |                   |       target                #
//#               busses   ...|                   | ...   busses                #
//#                           |                   |                             #
//#                       --->|                   |--->                         #
//#                           +-------------------+                             #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   July 30, 2018                                                             #
//#      - Initial release                                                      #
//###############################################################################
`default_nettype none

module WbXbc_xbar
  #(parameter ITR_CNT     = 4,   //number of initiator busses
    parameter TGT_CNT     = 4,   //number of target busses
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

    //Target address regions
    //----------------------
    input  wire [(TGT_CNT*ADDR_WIDTH)-1:0] region_addr,      //target address
    input  wire [(TGT_CNT*ADDR_WIDTH)-1:0] region_mask,      //selects relevant address bits

    //Initiator interface
    //-------------------
    input  wire [ITR_CNT-1:0]              itr_cyc_i,        //bus cycle indicator       +-
    input  wire [ITR_CNT-1:0]              itr_stb_i,        //access request            |
    input  wire [ITR_CNT-1:0]              itr_we_i,         //write enable              |
    input  wire [ITR_CNT-1:0]              itr_lock_i,       //uninterruptable bus cycle | initiator
    input  wire [(ITR_CNT*SEL_WIDTH)-1:0]  itr_sel_i,        //write data selects        | to
    input  wire [(ITR_CNT*ADDR_WIDTH)-1:0] itr_adr_i,        //address bus               | target
    input  wire [(ITR_CNT*DATA_WIDTH)-1:0] itr_dat_i,        //write data bus            |
    input  wire [ITR_CNT-1:0]              itr_tga_prio_i,   //access priorities         |
    input  wire [(ITR_CNT*TGA_WIDTH)-1:0]  itr_tga_i,        //generic address tags      |
    input  wire [(ITR_CNT*TGC_WIDTH)-1:0]  itr_tgc_i,        //bus cycle tags            |
    input  wire [(ITR_CNT*TGWD_WIDTH)-1:0] itr_tgd_i,        //write data tags           +-
    output wire [ITR_CNT-1:0]              itr_ack_o,        //bus cycle acknowledge     +-
    output wire [ITR_CNT-1:0]              itr_err_o,        //error indicator           | target
    output wire [ITR_CNT-1:0]              itr_rty_o,        //retry request             | to
    output wire [ITR_CNT-1:0]              itr_stall_o,      //access delay              | initiator
    output wire [(ITR_CNT*DATA_WIDTH)-1:0] itr_dat_o,        //read data bus             |
    output wire [(ITR_CNT*TGRD_WIDTH)-1:0] itr_tgd_o,        //read data tags            +-

    //Target interfaces
    //-----------------
    output wire [TGT_CNT-1:0]              tgt_cyc_o,        //bus cycle indicator       +-
    output wire [TGT_CNT-1:0]              tgt_stb_o,        //access request            |
    output wire [TGT_CNT-1:0]              tgt_we_o,         //write enable              |
    output wire [TGT_CNT-1:0]              tgt_lock_o,       //uninterruptable bus cycle | initiator
    output wire [(TGT_CNT*SEL_WIDTH)-1:0]  tgt_sel_o,        //write data selects        | to
    output wire [(TGT_CNT*ADDR_WIDTH)-1:0] tgt_adr_o,        //address bus               | target
    output wire [(TGT_CNT*DATA_WIDTH)-1:0] tgt_dat_o,        //write data bus            |
    output wire [(TGT_CNT*TGA_WIDTH)-1:0]  tgt_tga_o,        //propagated address tags   |
    output wire [(TGT_CNT*TGC_WIDTH)-1:0]  tgt_tgc_o,        //bus cycle tags            |
    output wire [(TGT_CNT*TGWD_WIDTH)-1:0] tgt_tgd_o,        //write data tags           +-
    input  wire [TGT_CNT-1:0]              tgt_ack_i,        //bus cycle acknowledge     +-
    input  wire [TGT_CNT-1:0]              tgt_err_i,        //error indicator           | target
    input  wire [TGT_CNT-1:0]              tgt_rty_i,        //retry request             | to
    input  wire [TGT_CNT-1:0]              tgt_stall_i,      //access delay              | initiator
    input  wire [(TGT_CNT*DATA_WIDTH)-1:0] tgt_dat_i,        //read data bus             |
    input  wire [(TGT_CNT*TGRD_WIDTH)-1:0] tgt_tgd_i);       //read data tags            +-

   //Example: 2x2 crossbar switch
   //============================
   //
   //    initiator A       initiator B
   //         |                 |
   //         V                 V
   //   +-----------+     +-----------+
   //   |   WbXbc   |     |   WbXbc   |
   //   |distributor|     |distributor|
   //   +-----------+     +-----------+
   //      |     |           |     |
   //      |     |           |     |   +---------+
   //      +---- | --------- | --- | ->|         |
   //            |           |     |   |  WbXbc  |--> target A
   //            |           |     |   | arbiter |
   //            |           +---- | ->|         |
   //            |                 |   +---------+
   //            |                 |
   //            |                 |   +---------+
   //            +---------------- | ->|         |
   //                              |   |  WbXbc  |--> target B
   //                              |   | arbiter |
   //                              +-->|         |
   //                                  +---------+

   //Crossbar busses
   //===============
   //Distributor buses:
   // MSB                                                                            LSB
   // [[         ITR n          ]...[         ITR 1          ][         ITR 0         ]]
   // [[[TGT n]...[TGT 1][TGT 0]]...[[TGT n]...[TGT 1][TGT 0]][[TGT n]...[TGT 1][TGT 0]]
   wire [(ITR_CNT*TGT_CNT)-1:0]               distributor_cyc_o;   //bus cycle indicator       +-
   wire [(ITR_CNT*TGT_CNT)-1:0]               distributor_stb_o;   //access request            |
   wire [(ITR_CNT*TGT_CNT)-1:0]               distributor_we_o;    //write enable              |
   wire [(ITR_CNT*TGT_CNT)-1:0]               distributor_lock_o;  //uninterruptable bus cycle | initiator
   wire [(ITR_CNT*TGT_CNT*SEL_WIDTH)-1:0]     distributor_sel_o;   //write data selects        | to
   wire [(ITR_CNT*TGT_CNT*ADDR_WIDTH)-1:0]    distributor_adr_o;   //address bus               | target
   wire [(ITR_CNT*TGT_CNT*DATA_WIDTH)-1:0]    distributor_dat_o;   //write data bus            |
   wire [(ITR_CNT*TGT_CNT*(TGA_WIDTH+1))-1:0] distributor_tga_o;   //address tags              |
   wire [(ITR_CNT*TGT_CNT*TGC_WIDTH)-1:0]     distributor_tgc_o;   //bus cycle tags            |
   wire [(ITR_CNT*TGT_CNT*TGWD_WIDTH)-1:0]    distributor_tgd_o;   //write data tags           +-
   reg  [(ITR_CNT*TGT_CNT)-1:0]               distributor_ack_i;   //bus cycle acknowledge     +-
   reg  [(ITR_CNT*TGT_CNT)-1:0]               distributor_err_i;   //error indicator           | target
   reg  [(ITR_CNT*TGT_CNT)-1:0]               distributor_rty_i;   //retry request             | to
   reg  [(ITR_CNT*TGT_CNT)-1:0]               distributor_stall_i; //access delay              | initiator
   reg  [(ITR_CNT*TGT_CNT*DATA_WIDTH)-1:0]    distributor_dat_i;   //read data bus             |
   reg  [(ITR_CNT*TGT_CNT*TGRD_WIDTH)-1:0]    distributor_tgd_i;   //read data tags            +-

   //Arbiter busses:
   // MSB                                                                            LSB
   // [[         TGT n          ]...[         TGT 1          ][         TGT 0         ]]
   // [[[ITR n]...[ITR 1][ITR 0]]...[[ITR n]...[ITR 1][ITR 0]][[ITR n]...[ITR 1][ITR 0]]
   reg  [(ITR_CNT*TGT_CNT)-1:0]               arbiter_cyc_i;       //bus cycle indicator       +-
   reg  [(ITR_CNT*TGT_CNT)-1:0]               arbiter_stb_i;       //access request            |
   reg  [(ITR_CNT*TGT_CNT)-1:0]               arbiter_we_i;        //write enable              |
   reg  [(ITR_CNT*TGT_CNT)-1:0]               arbiter_lock_i;      //uninterruptable bus cycle |
   reg  [(ITR_CNT*TGT_CNT*SEL_WIDTH)-1:0]     arbiter_sel_i;       //write data selects        | initiator
   reg  [(ITR_CNT*TGT_CNT*ADDR_WIDTH)-1:0]    arbiter_adr_i;       //address bus               | to
   reg  [(ITR_CNT*TGT_CNT*DATA_WIDTH)-1:0]    arbiter_dat_i;       //write data bus            | target
   reg  [(ITR_CNT*TGT_CNT)-1:0]               arbiter_tga_prio_i;  //access priorities         |
   reg  [(ITR_CNT*TGT_CNT*TGA_WIDTH)-1:0]     arbiter_tga_i;       //address tags              |
   reg  [(ITR_CNT*TGT_CNT*TGC_WIDTH)-1:0]     arbiter_tgc_i;       //bus cycle tags            |
   reg  [(ITR_CNT*TGT_CNT*TGWD_WIDTH)-1:0]    arbiter_tgd_i;       //write data tags           +-
   wire [(ITR_CNT*TGT_CNT)-1:0]               arbiter_ack_o;       //bus cycle acknowledge     +-
   wire [(ITR_CNT*TGT_CNT)-1:0]               arbiter_err_o;       //error indicator           | target
   wire [(ITR_CNT*TGT_CNT)-1:0]               arbiter_rty_o;       //retry request             | to
   wire [(ITR_CNT*TGT_CNT)-1:0]               arbiter_stall_o;     //access delay              | initiator
   wire [(ITR_CNT*TGT_CNT*DATA_WIDTH)-1:0]    arbiter_dat_o;       //read data bus             |
   wire [(ITR_CNT*TGT_CNT*TGRD_WIDTH)-1:0]    arbiter_tgd_o;       //read data tags            +-

   //Counters
   integer                                    k, l, m;

   //Instantiate distributors
   generate
      genvar                               i;
      for (i=0; i<ITR_CNT; i=i+1)
        begin
           WbXbc_distributor #(.TGT_CNT    (TGT_CNT),     //number of target busses
                               .ADDR_WIDTH (ADDR_WIDTH),  //width of the address bus
                               .DATA_WIDTH (DATA_WIDTH),  //width of each data bus
                               .SEL_WIDTH  (SEL_WIDTH),   //number of write data select lines
                               .TGA_WIDTH  (TGA_WIDTH+1), //number of propagated address tags
                               .TGC_WIDTH  (TGC_WIDTH),   //number of propagated cycle tags
                               .TGRD_WIDTH (TGRD_WIDTH),  //number of propagated read data tags
                               .TGWD_WIDTH (TGWD_WIDTH))  //number of propagated write data tags
           distributor

           (//Clock and reset
            //---------------
            .clk_i              (clk_i),                                                                      //module clock
            .async_rst_i        (async_rst_i),                                                                //asynchronous reset
            .sync_rst_i         (sync_rst_i),                                                                 //synchronous reset

            //Target address regions
            //----------------------
            .region_addr        (region_addr),                                                                //target address
            .region_mask        (region_mask),                                                                //selects relevant address bits

            //Initiator interface
            //-------------------
            .itr_cyc_i          (itr_cyc_i[i]),                                                               //bus cycle indicator       +-
            .itr_stb_i          (itr_stb_i[i]),                                                               //access request            |
            .itr_we_i           (itr_we_i[i]),                                                                //write enable              |
            .itr_lock_i         (itr_lock_i[i]),                                                              //uninterruptable bus cycle | initiator
            .itr_sel_i          (itr_sel_i[(SEL_WIDTH*(i+1))-1:(SEL_WIDTH*i)]),                               //write data selects        | initiator
            .itr_adr_i          (itr_adr_i[(ADDR_WIDTH*(i+1))-1:(ADDR_WIDTH*i)]),                             //address bus               | to
            .itr_dat_i          (itr_dat_i[(DATA_WIDTH*(i+1))-1:(DATA_WIDTH*i)]),                             //write data bus            | target
            .itr_tga_i          ({itr_tga_prio_i[i],                                                          //address tags              |
                                  itr_tga_i[(TGA_WIDTH*(i+1))-1:(TGA_WIDTH*i)]}),                             //                          |
            .itr_tgc_i          (itr_tgc_i[(TGC_WIDTH*(i+1))-1:(TGC_WIDTH*i)]),                               //bus cycle tags            |
            .itr_tgd_i          (itr_tgd_i[(TGWD_WIDTH*(i+1))-1:(TGWD_WIDTH*i)]),                             //write data tags           +-
            .itr_ack_o          (itr_ack_o[i]),                                                               //bus cycle acknowledge     +-
            .itr_err_o          (itr_err_o[i]),                                                               //error indicator           | target
            .itr_rty_o          (itr_rty_o[i]),                                                               //retry request             | to
            .itr_stall_o        (itr_stall_o[i]),                                                             //access delay              | initiator
            .itr_dat_o          (itr_dat_o[(DATA_WIDTH*(i+1))-1:(DATA_WIDTH*i)]),                             //read data bus             |
            .itr_tgd_o          (itr_tgd_o[(TGRD_WIDTH*(i+1))-1:(TGRD_WIDTH*i)]),                             //read data tags            +-

             //Target interfaces
             //-----------------
            .tgt_cyc_o          (distributor_cyc_o[(TGT_CNT*(i+1))-1:TGT_CNT*i]),                             //bus cycle indicator       +-
            .tgt_stb_o          (distributor_stb_o[(TGT_CNT*(i+1))-1:TGT_CNT*i]),                             //access request            |
            .tgt_we_o           (distributor_we_o[(TGT_CNT*(i+1))-1:TGT_CNT*i]),                              //write enable              |
            .tgt_lock_o         (distributor_lock_o[(TGT_CNT*(i+1))-1:TGT_CNT*i]),                            //uninterruptable bus cycle |
            .tgt_sel_o          (distributor_sel_o[(TGT_CNT*SEL_WIDTH*(i+1))-1:TGT_CNT*SEL_WIDTH*i]),         //write data selects        | initiator
            .tgt_adr_o          (distributor_adr_o[(TGT_CNT*ADDR_WIDTH*(i+1))-1:TGT_CNT*ADDR_WIDTH*i]),       //address bus               | to
            .tgt_dat_o          (distributor_dat_o[(TGT_CNT*DATA_WIDTH*(i+1))-1:TGT_CNT*DATA_WIDTH*i]),       //write data bus            | target
            .tgt_tga_o          (distributor_tga_o[(TGT_CNT*(TGA_WIDTH+1)*(i+1))-1:TGT_CNT*(TGA_WIDTH+1)*i]), //address tags              |
            .tgt_tgc_o          (distributor_tgc_o[(TGT_CNT*TGC_WIDTH*(i+1))-1:TGT_CNT*TGC_WIDTH*i]),         //bus cycle tags            |
            .tgt_tgd_o          (distributor_tgd_o[(TGT_CNT*TGWD_WIDTH*(i+1))-1:TGT_CNT*TGWD_WIDTH*i]),       //write data tags           +-
            .tgt_ack_i          (distributor_ack_i[(TGT_CNT*(i+1))-1:TGT_CNT*i]),                             //bus cycle acknowledge     +-
            .tgt_err_i          (distributor_err_i[(TGT_CNT*(i+1))-1:TGT_CNT*i]),                             //error indicator           | target
            .tgt_rty_i          (distributor_rty_i[(TGT_CNT*(i+1))-1:TGT_CNT*i]),                             //retry request             | to
            .tgt_stall_i        (distributor_stall_i[(TGT_CNT*(i+1))-1:TGT_CNT*i]),                           //access delay              | initiator
            .tgt_dat_i          (distributor_dat_i[(TGT_CNT*DATA_WIDTH*(i+1))-1:TGT_CNT*DATA_WIDTH*i]),       //read data bus             |
            .tgt_tgd_i          (distributor_tgd_i[(TGT_CNT*TGRD_WIDTH*(i+1))-1:TGT_CNT*TGRD_WIDTH*i]));      //read data tags            +-

        end
   endgenerate

   //Instantiate arbiters
   generate
      genvar                               j;
      for (j=0; j<ITR_CNT; j=j+1)
        begin
           WbXbc_arbiter #(.ITR_CNT    (ITR_CNT),     //number of initiator busses
                           .ADDR_WIDTH (ADDR_WIDTH),  //width of the address bus
                           .DATA_WIDTH (DATA_WIDTH),  //width of each data bus
                           .SEL_WIDTH  (SEL_WIDTH),   //number of write data select lines
                           .TGA_WIDTH  (TGA_WIDTH),   //number of propagated address tags
                           .TGC_WIDTH  (TGC_WIDTH),   //number of propagated cycle tags
                           .TGRD_WIDTH (TGRD_WIDTH),  //number of propagated read data tags
                           .TGWD_WIDTH (TGWD_WIDTH))  //number of propagated write data tags
           arbiter

           (//Clock and reset
            //---------------
            .clk_i              (clk_i),                                                              //module clock
            .async_rst_i        (async_rst_i),                                                        //asynchronous reset
            .sync_rst_i         (sync_rst_i),                                                         //synchronous reset

            //Initiator interface
            //-------------------
            .itr_cyc_i          (arbiter_cyc_i[(ITR_CNT*(j+1))-1:ITR_CNT*j]),                         //bus cycle indicator       +-
            .itr_stb_i          (arbiter_stb_i[(ITR_CNT*(j+1))-1:ITR_CNT*j]),                         //access request            |
            .itr_we_i           (arbiter_we_i[(ITR_CNT*(j+1))-1:ITR_CNT*j]),                          //write enable              |
            .itr_lock_i         (arbiter_lock_i[(ITR_CNT*(j+1))-1:ITR_CNT*j]),                        //uninterruptable bus cycle |
            .itr_sel_i          (arbiter_sel_i[(ITR_CNT*SEL_WIDTH*(j+1))-1:ITR_CNT*SEL_WIDTH*j]),     //write data selects        | initiator
            .itr_adr_i          (arbiter_adr_i[(ITR_CNT*ADDR_WIDTH*(j+1))-1:ITR_CNT*ADDR_WIDTH*j]),   //address bus               | to
            .itr_dat_i          (arbiter_dat_i[(ITR_CNT*DATA_WIDTH*(j+1))-1:ITR_CNT*DATA_WIDTH*j]),   //write data bus            | target
            .itr_tga_prio_i     (arbiter_tga_prio_i[(ITR_CNT*(j+1))-1:ITR_CNT*j]),                    //access priorities         |
            .itr_tga_i          (arbiter_tga_i[(ITR_CNT*TGA_WIDTH*(j+1))-1:ITR_CNT*TGA_WIDTH*j]),     //generic address tags      |
            .itr_tgc_i          (arbiter_tgc_i[(ITR_CNT*TGC_WIDTH*(j+1))-1:ITR_CNT*TGC_WIDTH*j]),     //bus cycle tags            |
            .itr_tgd_i          (arbiter_tgd_i[(ITR_CNT*TGWD_WIDTH*(j+1))-1:ITR_CNT*TGWD_WIDTH*j]),   //write data tags           +-
            .itr_ack_o          (arbiter_ack_o[(ITR_CNT*(j+1))-1:ITR_CNT*j]),                         //bus cycle acknowledge     +-
            .itr_err_o          (arbiter_err_o[(ITR_CNT*(j+1))-1:ITR_CNT*j]),                         //error indicator           | target
            .itr_rty_o          (arbiter_rty_o[(ITR_CNT*(j+1))-1:ITR_CNT*j]),                         //retry request             | to
            .itr_stall_o        (arbiter_stall_o[(ITR_CNT*(j+1))-1:ITR_CNT*j]),                       //access delay              | initiator
            .itr_dat_o          (arbiter_dat_o[(ITR_CNT*DATA_WIDTH*(j+1))-1:ITR_CNT*DATA_WIDTH*j]),   //read data bus             |
            .itr_tgd_o          (arbiter_tgd_o[(ITR_CNT*TGRD_WIDTH*(j+1))-1:ITR_CNT*TGRD_WIDTH*j]),   //read data tags            +-

            //Target interfaces
            //-----------------
            .tgt_cyc_o          (tgt_cyc_o[j]),                                                       //bus cycle indicator       +-
            .tgt_stb_o          (tgt_stb_o[j]),                                                       //access request            |
            .tgt_we_o           (tgt_we_o[j]),                                                        //write enable              |
            .tgt_lock_o         (tgt_lock_o[j]),                                                      //uninterruptable bus cycle | initiator
            .tgt_sel_o          (tgt_sel_o[(SEL_WIDTH*(j+1))-1:(SEL_WIDTH*j)]),                       //write data selects        | to
            .tgt_adr_o          (tgt_adr_o[(ADDR_WIDTH*(j+1))-1:(ADDR_WIDTH*j)]),                     //address bus               | target
            .tgt_dat_o          (tgt_dat_o[(DATA_WIDTH*(j+1))-1:(DATA_WIDTH*j)]),                     //write data bus            |
            .tgt_tga_o          (tgt_tga_o[(TGA_WIDTH*(j+1))-1:(TGA_WIDTH*j)]),                       //propagated address tags   |
            .tgt_tgc_o          (tgt_tgc_o[(TGC_WIDTH*(j+1))-1:(TGC_WIDTH*j)]),                       //bus cycle tags            |
            .tgt_tgd_o          (tgt_tgd_o[(TGWD_WIDTH*(j+1))-1:(TGWD_WIDTH*j)]),                     //write data tags           +-
            .tgt_ack_i          (tgt_ack_i[j]),                                                       //bus cycle acknowledge     +-
            .tgt_err_i          (tgt_err_i[j]),                                                       //error indicator           | target
            .tgt_rty_i          (tgt_rty_i[j]),                                                       //retry request             | to
            .tgt_stall_i        (tgt_stall_i[j]),                                                     //access delay              | initiator
            .tgt_dat_i          (tgt_dat_i[(DATA_WIDTH*(j+1))-1:(DATA_WIDTH*j)]),                     //read data bus             |
            .tgt_tgd_i          (tgt_tgd_i[(TGRD_WIDTH*(j+1))-1:(TGRD_WIDTH*j)]));                    //read data tags            +-

        end
   endgenerate

   //Crossbar connections
   always @*
     for (k=0; k<ITR_CNT; k=k+1)
     for (l=0; l<TGT_CNT; l=l+1)
       begin
          arbiter_cyc_i[(ITR_CNT*l)+k]         = distributor_cyc_o[(TGT_CNT*k)+l];                    //bus cycle indicator       +-
          arbiter_stb_i[(ITR_CNT*l)+k]         = distributor_stb_o[(TGT_CNT*k)+l];                    //access request            |
          arbiter_we_i[(ITR_CNT*l)+k]          = distributor_we_o[(TGT_CNT*k)+l];                     //write enable              |
          arbiter_lock_i[(ITR_CNT*l)+k]        = distributor_lock_o[(TGT_CNT*k)+l];                   //uninterruptable bus cycle |
          for (m=0; m<SEL_WIDTH; m=m+1)                                                               //write data selects        |
            arbiter_sel_i[(ITR_CNT*l)+k+m]     = distributor_sel_o[(TGT_CNT*k)+l+m];                  //                          |
          for (m=0; m<ADDR_WIDTH; m=m+1)                                                              //address bus               | initiator
            arbiter_adr_i[(ITR_CNT*l)+k+m]     = distributor_adr_o[(TGT_CNT*k)+l+m];                  //                          | to
          for (m=0; m<DATA_WIDTH; m=m+1)                                                              //write data bus            | target
            arbiter_dat_i[(ITR_CNT*l)+k+m]     = distributor_dat_o[(TGT_CNT*k)+l+m];                  //                          |
          for (m=0; m<TGA_WIDTH; m=m+1)                                                               //address tags              |
            arbiter_tga_i[(ITR_CNT*l)+k+m]     = distributor_tga_o[(TGT_CNT*k)+l+m];                  //                          |
          for (m=0; m<TGC_WIDTH; m=m+1)                                                               //bus cycle tags            |
            arbiter_tgc_i[(ITR_CNT*l)+k+m]     = distributor_tgc_o[(TGT_CNT*k)+l+m];                  //                          |
          for (m=0; m<TGWD_WIDTH; m=m+1)                                                              //write data tags           |
            arbiter_tgd_i[(ITR_CNT*l)+k+m]     = distributor_tgd_o[(TGT_CNT*k)+l+m];                  //                          +-

          distributor_ack_i[(TGT_CNT*k)+l]     = arbiter_ack_o[(ITR_CNT*l)+k];                        //bus cycle acknowledge     +-
          distributor_err_i[(TGT_CNT*k)+l]     = arbiter_err_o[(ITR_CNT*l)+k];                        //error indicator           |
          distributor_rty_i[(TGT_CNT*k)+l]     = arbiter_rty_o[(ITR_CNT*l)+k];                        //retry request             | target
          distributor_stall_i[(TGT_CNT*k)+l]   = arbiter_stall_o[(ITR_CNT*l)+k];                      //access delay              | to
          for (m=0; m<DATA_WIDTH; m=m+1)                                                              //read data bus             | initiator
            distributor_dat_i[(TGT_CNT*k)+l+m] = arbiter_dat_o[(ITR_CNT*l)+k+m];                      //                          |
          for (m=0; m<TGRD_WIDTH; m=m+1)                                                              //read data tags            |
            distributor_tgd_i[(TGT_CNT*k)+l+m] = arbiter_tgd_o[(ITR_CNT*l)+k+m];                      //                          +-

       end // for (l=0; l<TGT_CNT; l=l+1)

endmodule // WbXbc_xbar
