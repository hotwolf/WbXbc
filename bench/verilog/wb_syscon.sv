//###############################################################################
//# WbXbc - Wishbone SYSCON signal constraints                                  #
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
//#    This module contains contraints for Wishbone SYSCOB signals.             #
//#                                                                             #
//###############################################################################
//# Version History:                                                            #
//#   October 22, 2018                                                          #
//#      - Initial release                                                      #
//###############################################################################
`default_nettype none

module wb_syscon
   (//Clock and reset
    //---------------
    input wire                             fast_clk_i,       //fast input clock
    input wire                             slow_clk_i,       //slow input clock
    input wire                             sync_i,           //clock sync signal
    input wire                             async_rst_i,      //asynchronous reset
    input wire                             sync_rst_i);      //synchronous reset

   //State Machine
   //=============
   //        ______     ______     ______     ______            
   // init  /      \   /      \-->/      \-->/      \
   //  O--->| RST0 |-->| RST2 |   | CLK0 |   | CLK3 |       
   //       \______/   \______/<--\______/<--\______/                                      
   //         |  ^                / |  ^
   //         |  |               /  |  |
   //        _V__|_             /  _V__|_                       
   //       /      \           /  /      \                
   //       | RST1 |<---------/   | CLK1 |                  
   //       \______/              \______/                                                 
   //                      
   //State variable
   reg [2:0] 				   state_reg;        //state variable
   reg [2:0] 				   state_next        //next statr    

   //State encoding
   parameter STATE_RST0 = 3'b000;                            //reset, clocks low
   parameter STATE_RST1 = 3'b001;                            //reset, fast clock only
   parameter STATE_RST2 = 3'b010;                            //reset, both clocks
   parameter STATE_CLK0 = 3'b100;                            //out oreset, clocks low
   parameter STATE_CLK1 = 3'b101;                            //out of reset, fast clock only
   parameter STATE_CLK2 = 3'b110;                            //out of reset, both vlocks

   //State transitions
   always *
     case (state_reg)
       STATE_RST0:
	 begin
	    assume(~fast_clk_i);
	    assume(~slow_clk_i);
	    
	    

	 end
       
   
   
   //Reset condition
   //===============
   initial
     begin
        prev_clk_i       = 1'b0;                             //initialize prev. clock state
        prev_async_rst_i = 1'b1;                             //initialize prev. clock state
        prev_sync_rst_i  = 1'b1;                             //initialize prev. clock state
        assume (clk_i);                                      //module clock
        assume (async_rst_i);                                //asynchronous reset
        assume (sync_rst_i);                                 //synchronous reset
     end

   //Expect free-running clock
   //=========================
   always @($global_clock)
     begin                                                   //toggle clock input
        assume (clk_i ^ prev_clk_i);
        prev_clk_i <= clk_i;
     end

   //Only toggle at clock events
   //===========================
   always @($global_clock)
     if ( 

     begin
	prev_async_rst_i = async_rst_i;                      //capture prev. clock state
	prev_sync_rst_i  = sync_rst_i;                       //capture prev. clock state
     end

   always @(negedge clk_i)
     begin
	assume (~^(prev_async_rst_i, async_rst_i);           //keep reset stable at negedge
	assume (~^(prev_sync_rst_i,  sync_rst_i);            //keep reset stable at negedge
     end
   
endmodule // wb_syscon
