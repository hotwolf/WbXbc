//###############################################################################
//# WbXbc - Wishbone Crossbar Components - Bus Distributor                      #
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
//#    This module combines an address decoder, an error generator, and a bus   #
//#    splitter for the pipelined Wishbone protocol.                            #
//#                                                                             #
//#                           +-------------------+                             #
//#               address --->|                   |                             #
//#               regions     |                   |                             #
//#                           |                   |                             #
//#                           |                   |--->                         #
//#                           |       WbXbc       |                             #
//#              single       |    distributor    |--->  multiple               #
//#             initiator --->|                   |       target                #
//#               bus         |                   | ...   busses                #
//#                           |                   |                             #
//#                           |                   |--->                         #
//#                           +-------------------+                             #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   July 30, 2018                                                             #
//#      - Initial release                                                      #
//#   October 8, 2018                                                           #
//#      - Updated parameter and signal naming                                  #
//###############################################################################
`default_nettype none

module WbXbc_distributor
  #(parameter TGT_CNT     = 4,   //number of target busses
    parameter ADR_WIDTH   = 16,  //width of the address bus
    parameter DAT_WIDTH   = 16,  //width of each data bus
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
    input  wire [(TGT_CNT*ADR_WIDTH)-1:0]  region_adr_i,     //target address
    input  wire [(TGT_CNT*ADR_WIDTH)-1:0]  region_msk_i,     //selects relevant address bits

    //Initiator interface
    //-------------------
    input  wire                            itr_cyc_i,        //bus cycle indicator       +-
    input  wire                            itr_stb_i,        //access request            |
    input  wire                            itr_we_i,         //write enable              |
    input  wire                            itr_lock_i,       //uninterruptable bus cycle |
    input  wire [SEL_WIDTH-1:0]            itr_sel_i,        //write data selects        | initiator
    input  wire [ADR_WIDTH-1:0]            itr_adr_i,        //address bus               | to
    input  wire [DAT_WIDTH-1:0]            itr_dat_i,        //write data bus            | target
    input  wire [TGA_WIDTH-1:0]            itr_tga_i,        //generic address tags      |
    input  wire [TGC_WIDTH-1:0]            itr_tgc_i,        //bus cycle tags            |
    input  wire [TGWD_WIDTH-1:0]           itr_tgd_i,        //write data tags           +-
    output wire                            itr_ack_o,        //bus cycle acknowledge     +-
    output wire                            itr_err_o,        //error indicator           | target
    output wire                            itr_rty_o,        //retry request             | to
    output wire                            itr_stall_o,      //access delay              | initiator
    output wire [DAT_WIDTH-1:0]            itr_dat_o,        //read data bus             |
    output wire [TGRD_WIDTH-1:0]           itr_tgd_o,        //read data tags            +-

    //Target interfaces
    //-----------------
    output wire [TGT_CNT-1:0]              tgt_cyc_o,        //bus cycle indicator       +-
    output wire [TGT_CNT-1:0]              tgt_stb_o,        //access request            |
    output wire [TGT_CNT-1:0]              tgt_we_o,         //write enable              |
    output wire [TGT_CNT-1:0]              tgt_lock_o,       //uninterruptable bus cycle | initiator
    output wire [(TGT_CNT*SEL_WIDTH)-1:0]  tgt_sel_o,        //write data selects        | to
    output wire [(TGT_CNT*ADR_WIDTH)-1:0]  tgt_adr_o,        //address bus               | target
    output wire [(TGT_CNT*DAT_WIDTH)-1:0]  tgt_dat_o,        //write data bus            |
    output wire [(TGT_CNT*TGA_WIDTH)-1:0]  tgt_tga_o,        //propagated address tags   |
    output wire [(TGT_CNT*TGC_WIDTH)-1:0]  tgt_tgc_o,        //bus cycle tags            |
    output wire [(TGT_CNT*TGWD_WIDTH)-1:0] tgt_tgd_o,        //write data tags           +-
    input  wire [TGT_CNT-1:0]              tgt_ack_i,        //bus cycle acknowledge     +-
    input  wire [TGT_CNT-1:0]              tgt_err_i,        //error indicator           | target
    input  wire [TGT_CNT-1:0]              tgt_rty_i,        //retry request             | to
    input  wire [TGT_CNT-1:0]              tgt_stall_i,      //access delay              | initiator
    input  wire [(TGT_CNT*DAT_WIDTH)-1:0]  tgt_dat_i,        //read data bus             |
    input  wire [(TGT_CNT*TGRD_WIDTH)-1:0] tgt_tgd_i);       //read data tags            +-

   //     initiator
   //         |
   //         V
   //   +-----------+
   //   |   WbXbc   |
   //   |  address  |
   //   |  decoder  |
   //   +-----------+
   //         | adec
   //         V  bus
   //   +-----------+
   //   |   WbXbc   |
   //   |   error   |
   //   | generator |
   //   +-----------+
   //         | errgen
   //         V  bus
   //   +-----------+
   //   |  WbXbc    |
   //   | splitter  |
   //   +-----------+
   //      | ... |
   //      V     V
   //      targets

   //Internal Wishbone busses
   //Address decoder busses
   wire                                    adec_cyc;            //bus cycle indicator       +-
   wire                                    adec_stb;            //access request            |
   wire                                    adec_we;             //write enable              |
   wire                                    adec_lock;           //uninterruptable bus cycle |
   wire [SEL_WIDTH-1:0]                    adec_sel;            //write data selects        | initiator
   wire [ADR_WIDTH-1:0]                    adec_adr;            //address bus               | to
   wire [DAT_WIDTH-1:0]                    adec_wdat;           //write data bus            | target
   wire [TGT_CNT-1:0]                      adec_tga_tgtsel;     //access priorities         |
   wire [TGA_WIDTH-1:0]                    adec_tga;            //generic address tags      |
   wire [TGC_WIDTH-1:0]                    adec_tgc;            //bus cycle tags            |
   wire [TGWD_WIDTH-1:0]                   adec_tgwd;           //write data tags           +-
   wire                                    adec_ack;            //bus cycle acknowledge     +-
   wire                                    adec_err;            //error indicator           | target
   wire                                    adec_rty;            //retry request             | to
   wire                                    adec_stall;          //access delay              | initiator
   wire [DAT_WIDTH-1:0]                    adec_rdat;           //read data bus             |
   wire [TGRD_WIDTH-1:0]                   adec_tgrd;           //read data tags            +-

   //Error generator busses
   wire                                    errgen_cyc;          //bus cycle indicator       +-
   wire                                    errgen_stb;          //access request            |
   wire                                    errgen_we;           //write enable              |
   wire                                    errgen_lock;         //uninterruptable bus cycle |
   wire [SEL_WIDTH-1:0]                    errgen_sel;          //write data selects        | initiator
   wire [ADR_WIDTH-1:0]                    errgen_adr;          //address bus               | to
   wire [DAT_WIDTH-1:0]                    errgen_wdat;         //write data bus            | target
   wire [TGT_CNT-1:0]                      errgen_tga_tgtsel;   //access priorities         |
   wire [TGA_WIDTH-1:0]                    errgen_tga;          //generic address tags      |
   wire [TGC_WIDTH-1:0]                    errgen_tgc;          //bus cycle tags            |
   wire [TGWD_WIDTH-1:0]                   errgen_tgwd;         //write data tags           +-
   wire                                    errgen_ack;          //bus cycle acknowledge     +-
   wire                                    errgen_err;          //error indicator           | target
   wire                                    errgen_rty;          //retry request             | to
   wire                                    errgen_stall;        //access delay              | initiator
   wire [DAT_WIDTH-1:0]                    errgen_rdat;         //read data bus             |
   wire [TGRD_WIDTH-1:0]                   errgen_tgrd;         //read data tags            +-

   //Address decoder
   WbXbc_address_decoder #(.TGT_CNT    (TGT_CNT),               //number of target addresses to decode
                           .ADR_WIDTH  (ADR_WIDTH),             //width of the address bus
                           .DAT_WIDTH  (DAT_WIDTH),             //width of each data bus
                           .SEL_WIDTH  (SEL_WIDTH),             //number of write data select lines
                           .TGA_WIDTH  (TGA_WIDTH),             //number of propagated address tags
                           .TGC_WIDTH  (TGC_WIDTH),             //number of propagated cycle tags
                           .TGRD_WIDTH (TGRD_WIDTH),            //number of propagated read data tags
                           .TGWD_WIDTH (TGWD_WIDTH))            //number of propagated write data tags
   adec
           (//Target address regions
            //----------------------
            .region_adr_i       (region_adr_i),                 //target address
            .region_msk_i       (region_msk_i),                 //selects relevant address bits

            //Initiator interface
            //-------------------
            .itr_cyc_i          (itr_cyc_i),                    //bus cycle indicator       +-
            .itr_stb_i          (itr_stb_i),                    //access request            |
            .itr_we_i           (itr_we_i),                     //write enable              |
            .itr_lock_i         (itr_lock_i),                   //uninterruptable bus cycle | initiator
            .itr_sel_i          (itr_sel_i),                    //write data selects        | initiator
            .itr_adr_i          (itr_adr_i),                    //address bus               | to
            .itr_dat_i          (itr_dat_i),                    //write data bus            | target
            .itr_tga_i          (itr_tga_i),                    //address tags              |
            .itr_tgc_i          (itr_tgc_i),                    //bus cycle tags            |
            .itr_tgd_i          (itr_tgd_i),                    //write data tags           +-
            .itr_ack_o          (itr_ack_o),                    //bus cycle acknowledge     +-
            .itr_err_o          (itr_err_o),                    //error indicator           | target
            .itr_rty_o          (itr_rty_o),                    //retry request             | to
            .itr_stall_o        (itr_stall_o),                  //access delay              | initiator
            .itr_dat_o          (itr_dat_o),                    //read data bus             |
            .itr_tgd_o          (itr_tgd_o),                    //read data tags            +-

             //Target interface
             //----------------
            .tgt_cyc_o          (adec_cyc),                     //bus cycle indicator       +-
            .tgt_stb_o          (adec_stb),                     //access request            |
            .tgt_we_o           (adec_we),                      //write enable              |
            .tgt_lock_o         (adec_lock),                    //uninterruptable bus cycle |
            .tgt_sel_o          (adec_sel),                     //write data selects         | initiator
            .tgt_adr_o          (adec_adr),                     //write data selects        | to
            .tgt_dat_o          (adec_wdat),                    //write data bus            | target
            .tgt_tga_o          (adec_tga),                     //address tags              |
            .tgt_tga_tgtsel_o   (adec_tga_tgtsel),              //target select tags        |
            .tgt_tgc_o          (adec_tgc),                     //bus cycle tags            |
            .tgt_tgd_o          (adec_tgwd),                    //write data tags           +-
            .tgt_ack_i          (adec_ack),                     //bus cycle acknowledge     +-
            .tgt_err_i          (adec_err),                     //error indicator           | target
            .tgt_rty_i          (adec_rty),                     //retry request             | to
            .tgt_stall_i        (adec_stall),                   //access delay              | initiator
            .tgt_dat_i          (adec_rdat),                    //read data bus             |
            .tgt_tgd_i          (adec_tgrd));                   //read data tags            +-


   //Error generator
   WbXbc_error_generator #(.TGT_CNT    (TGT_CNT),               //number of target addresses to decode
                           .ADR_WIDTH  (ADR_WIDTH),             //width of the address bus
                           .DAT_WIDTH  (DAT_WIDTH),             //width of each data bus
                           .SEL_WIDTH  (SEL_WIDTH),             //number of write data select lines
                           .TGA_WIDTH  (TGA_WIDTH),             //number of propagated address tags
                           .TGC_WIDTH  (TGC_WIDTH),             //number of propagated cycle tags
                           .TGRD_WIDTH (TGRD_WIDTH),            //number of propagated read data tags
                           .TGWD_WIDTH( TGWD_WIDTH))            //number of propagated write data tags
   errgen 
           (//Clock and reset
            //---------------
            .clk_i               (clk_i),                       //module clock
            .async_rst_i         (clk_i),                       //asynchronous reset
            .sync_rst_i          (sync_rst_i),                  //synchronous reset

            //Initiator interface
            //-------------------
            .itr_cyc_i           (adec_cyc),                    //bus cycle indicator       +-
            .itr_stb_i           (adec_stb),                    //access request            |
            .itr_we_i            (adec_we),                     //write enable              |
            .itr_lock_i          (adec_lock),                   //uninterruptable bus cycle | initiator
            .itr_sel_i           (adec_sel),                    //write data selects        | initiator
            .itr_adr_i           (adec_adr),                    //address bus               | to
            .itr_dat_i           (adec_wdat),                   //write data bus            | target
            .itr_tga_i           (adec_tga),                    //address tags              |
            .itr_tga_tgtsel_i    (adec_tga_tgtsel),             //target select tags        |
            .itr_tgc_i           (adec_tgc),                    //bus cycle tags            |
            .itr_tgd_i           (adec_tgwd),                   //write data tags           +-
            .itr_ack_o           (adec_ack),                    //bus cycle acknowledge     +-
            .itr_err_o           (adec_err),                    //error indicator           | target
            .itr_rty_o           (adec_rty),                    //retry request             | to
            .itr_stall_o         (adec_stall),                  //access delay              | initiator
            .itr_dat_o           (adec_rdat),                   //read data bus             |
            .itr_tgd_o           (adec_tgrd),                   //read data tags            +-

            //Target interfaces
            //-----------------
            .tgt_cyc_o           (errgen_cyc),                  //bus cycle indicator       +-
            .tgt_stb_o           (errgen_stb),                  //access request            |
            .tgt_we_o            (errgen_we),                   //write enable              |
            .tgt_lock_o          (errgen_lock),                 //uninterruptable bus cycle |
            .tgt_sel_o           (errgen_sel),                  //write data selects        | initiator
            .tgt_adr_o           (errgen_adr),                  //write data selects        | to
            .tgt_dat_o           (errgen_wdat),                 //write data bus            | target
            .tgt_tga_o           (errgen_tga),                  //address tags              |
            .tgt_tga_tgtsel_o    (errgen_tga_tgtsel),           //target select tags        |
            .tgt_tgc_o           (errgen_tgc),                  //bus cycle tags            |
            .tgt_tgd_o           (errgen_tgwd),                 //write data tags           +-
            .tgt_ack_i           (errgen_ack),                  //bus cycle acknowledge     +-
            .tgt_err_i           (errgen_err),                  //error indicator           | target
            .tgt_rty_i           (errgen_rty),                  //retry request             | to
            .tgt_stall_i         (errgen_stall),                //access delay              | initiator
            .tgt_dat_i           (errgen_rdat),                 //read data bus             |
            .tgt_tgd_i           (errgen_tgrd));                //read data tags            +-


   //Bus splitter
   WbXbc_splitter #(.TGT_CNT    (TGT_CNT),                      //number of target addresses to decode
                    .ADR_WIDTH  (ADR_WIDTH),                    //width of the address bus
                    .DAT_WIDTH  (DAT_WIDTH),                    //width of each data bus
                    .SEL_WIDTH  (SEL_WIDTH),                    //number of write data select lines
                    .TGA_WIDTH  (TGA_WIDTH),                    //number of propagated address tags
                    .TGC_WIDTH  (TGC_WIDTH),                    //number of propagated cycle tags
                    .TGRD_WIDTH (TGRD_WIDTH),                   //number of propagated read data tags
                    .TGWD_WIDTH (TGWD_WIDTH))                   //number of propagated write data tags
   split
           (//Clock and reset
            //---------------
            .clk_i               (clk_i),                       //module clock
            .async_rst_i         (clk_i),                       //asynchronous reset
            .sync_rst_i          (sync_rst_i),                  //synchronous reset

            //Initiator interface
            //-------------------
            .itr_cyc_i          (errgen_cyc),                   //bus cycle indicator       +-
            .itr_stb_i          (errgen_stb),                   //access request            |
            .itr_we_i           (errgen_we),                    //write enable              |
            .itr_lock_i         (errgen_lock),                  //uninterruptable bus cycle |
            .itr_sel_i          (errgen_sel),                   //write data selects        | initiator
            .itr_adr_i          (errgen_adr),                   //address bus               | to
            .itr_dat_i          (errgen_wdat),                  //write data bus            | target
            .itr_tga_i          (errgen_tga),                   //tags from address decoder |
            .itr_tga_tgtsel_i   (errgen_tga_tgtsel),            //generic address tags      |
            .itr_tgc_i          (errgen_tgc),                   //bus cycle tags            |
            .itr_tgd_i          (errgen_tgwd),                  //write data tags           +-
            .itr_ack_o          (errgen_ack),                   //bus cycle acknowledge     +-
            .itr_err_o          (errgen_err),                   //error indicator           | target
            .itr_rty_o          (errgen_rty),                   //retry request             | to
            .itr_stall_o        (errgen_stall),                 //access delay              | initiator
            .itr_dat_o          (errgen_rdat),                  //read data bus             |
            .itr_tgd_o          (errgen_tgrd),                  //read data tags            +-

            //Target interfaces
            //-----------------
            .tgt_cyc_o          (tgt_cyc_o),                    //bus cycle indicator       +-
            .tgt_stb_o          (tgt_stb_o),                    //access request            |
            .tgt_we_o           (tgt_we_o),                     //write enable              |
            .tgt_lock_o         (tgt_lock_o),                   //uninterruptable bus cycle | initiator
            .tgt_sel_o          (tgt_sel_o),                    //write data selects        | to
            .tgt_adr_o          (tgt_adr_o),                    //address bus               | target
            .tgt_dat_o          (tgt_dat_o),                    //write data bus            |
            .tgt_tga_o          (tgt_tga_o),                    //propagated address tags   |
            .tgt_tgc_o          (tgt_tgc_o),                    //bus cycle tags            |
            .tgt_tgd_o          (tgt_tgd_o),                    //write data tags           +-
            .tgt_ack_i          (tgt_ack_i),                    //bus cycle acknowledge     +-
            .tgt_err_i          (tgt_err_i),                    //error indicator           | target
            .tgt_rty_i          (tgt_rty_i),                    //retry request             | to
            .tgt_stall_i        (tgt_stall_i),                  //access delay              | initiator
            .tgt_dat_i          (tgt_dat_i),                    //read data bus             |
            .tgt_tgd_i          (tgt_tgd_i));                   //read data tags            +-

endmodule // WbXbc_distributor
