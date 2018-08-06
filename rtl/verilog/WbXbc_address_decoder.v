//###############################################################################
//# WbXbc - Wishbone Crossbar Components - Bus Address Decoder                  #
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
//#    This module implements an address decoder for the Wishbone protocol. It  #
//#    propagates accesses from the initiator bus to the target bus and adds a  #
//#    set of address tags which selecting the target block.                    #
//#                                                                             #
//#                            +-------------------+                            #
//#               address  --->|                   |                            #
//#               regions      |                   |                            #
//#                            |       WbXbc       |       target               #
//#              initiator     |      address      |--->    bus                 #
//#                 bus    --->|      decoder      |        with                #
//#                w/out       |                   |       selects              #
//#               selects      |                   |                            #
//#                            +-------------------+                            #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   July 18, 2018                                                             #
//#      - Initial release                                                      #
//###############################################################################
`default_nettype none

module WbXbc_address_decoder
  #(parameter TGT_CNT     = 4,   //number of target addresses to decode
    parameter ADDR_WIDTH  = 16,  //width of the address bus
    parameter DATA_WIDTH  = 8,   //width of each data bus
    parameter SEL_WIDTH   = 2,   //number of write data select lines
    parameter TGA_WIDTH   = 1,   //number of propagated address tags
    parameter TGC_WIDTH   = 1,   //number of propagated cycle tags
    parameter TGRD_WIDTH  = 1,   //number of propagated read data tags
    parameter TGWD_WIDTH  = 1)   //number of propagated write data tags

   (//Target address regions
    //----------------------
    input  wire [(TGT_CNT*ADDR_WIDTH)-1:0] region_addr,      //target address
    input  wire [(TGT_CNT*ADDR_WIDTH)-1:0] region_mask,      //selects relevant address bits
                                                             //(1: relevant, 0: ignored)

    //Initiator interface
    //-------------------
    input  wire                            itr_cyc_i,        //bus cycle indicator       +-
    input  wire                            itr_stb_i,        //access request            |
    input  wire                            itr_we_i,         //write enable              |
    input  wire                            itr_lock_i,       //uninterruptable bus cycle | initiator
    input  wire [SEL_WIDTH-1:0]            itr_sel_i,        //write data selects        | initiator
    input  wire [ADDR_WIDTH-1:0]           itr_adr_i,        //address bus               | to
    input  wire [DATA_WIDTH-1:0]           itr_dat_i,        //write data bus            | target
    input  wire [TGA_WIDTH-1:0]            itr_tga_i,        //address tags              |
    input  wire [TGC_WIDTH-1:0]            itr_tgc_i,        //bus cycle tags            |
    input  wire [TGWD_WIDTH-1:0]           itr_tgd_i,        //write data tags           +-
    output wire                            itr_ack_o,        //bus cycle acknowledge     +-
    output wire                            itr_err_o,        //error indicator           | target
    output wire                            itr_rty_o,        //retry request             | to
    output wire                            itr_stall_o,      //access delay              | initiator
    output wire [DATA_WIDTH-1:0]           itr_dat_o,        //read data bus             |
    output wire [TGRD_WIDTH-1:0]           itr_tgd_o,        //read data tags            +-

    //Target interface
    //----------------
    output wire                            tgt_cyc_o,        //bus cycle indicator       +-
    output wire                            tgt_stb_o,        //access request            |
    output wire                            tgt_we_o,         //write enable              |
    output wire                            tgt_lock_o,       //uninterruptable bus cycle |
    output wire [SEL_WIDTH-1:0]            tgt_sel_o,        //write data selects        | initiator
    output wire [ADDR_WIDTH-1:0]           tgt_adr_o,        //write data selects        | to
    output wire [DATA_WIDTH-1:0]           tgt_dat_o,        //write data bus            | target
    output wire [TGA_WIDTH-1:0]            tgt_tga_o,        //address tags              |
    output reg  [TGT_CNT-1:0]              itr_tga_tgtsel_o, //target select tags        |
    output wire [TGC_WIDTH-1:0]            tgt_tgc_o,        //bus cycle tags            |
    output wire [TGWD_WIDTH-1:0]           tgt_tgd_o,        //write data tags           +-
    input  wire                            tgt_ack_i,        //bus cycle acknowledge     +-
    input  wire                            tgt_err_i,        //error indicator           | target
    input  wire                            tgt_rty_i,        //retry request             | to
    input  wire                            tgt_stall_i,      //access delay              | initiator
    input  wire [DATA_WIDTH-1:0]           tgt_dat_i,        //read data bus             |
    input  wire [TGRD_WIDTH-1:0]           tgt_tgd_i);       //read data tags            +-

   //Counters
   integer            i;

   //Address decoding
   always @*                                                 //target select tags
   //always @(itr_adr_i or region_addr or region_mask)       //target select tags
     begin
        itr_tga_tgtsel_o = {TGT_CNT{1'b1}};
        for (i=0; i<(TGT_CNT*ADDR_WIDTH); i=i+1)
          itr_tga_tgtsel_o[i/ADDR_WIDTH] = itr_tga_tgtsel_o[i/ADDR_WIDTH] &
                                          ~((region_addr[i] ^ itr_adr_i[i%ADDR_WIDTH]) & region_mask[i]);
     end

   //Plain signal propagation to the target bus
   assign tgt_cyc_o   = itr_cyc_i;  //bus cycle indicator
   assign tgt_stb_o   = itr_stb_i;  //access request
   assign tgt_lock_o  = itr_lock_i; //uninterruptible bus cycle indicators
   assign tgt_we_o    = itr_we_i;   //write enable
   assign tgt_sel_o   = itr_sel_i;  //write data selects
   assign tgt_adr_o   = itr_adr_i;  //address bus
   assign tgt_dat_o   = itr_dat_i;  //write data bus
   assign tgt_tga_o   = itr_tga_i;  //address tags
   assign tgt_tgc_o   = itr_tgc_i;  //bus cycle tags
   assign tgt_tgd_o   = itr_tgd_i;  //write data tags

   //Plain signal propagation to the initiator bus
   assign itr_ack_o   = tgt_ack_i;   //bus cycle acknowledge
   assign itr_err_o   = tgt_err_i;   //error indicator
   assign itr_rty_o   = tgt_rty_i;   //retry request
   assign itr_stall_o = tgt_stall_i; //access delay
   assign itr_dat_o   = tgt_dat_i;   //read data bus
   assign itr_tgd_o   = tgt_tgd_i;   //read data tags

endmodule // WbXbc_address_decoder
