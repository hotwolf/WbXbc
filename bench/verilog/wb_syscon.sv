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
//#   October 30, 2018                                                          #
//#      - Added gated clock support                                            #
//###############################################################################
`default_nettype none

module wb_syscon
   (//Clock and reset
    //---------------
    input  wire                       clk_i,              //clock input
    input  wire                       sync_i,             //clock enable
    input  wire                       async_rst_i,        //asynchronous reset
    input  wire                       sync_rst_i,         //synchronous reset
    output reg                        gated_clk_o);       //gated clock
   
   //Reset delay
   reg  [1:0]                         por_cnt;       //reset counter         
                                                      
   //Clock state                                       
   reg                                clk_reg = 2'b00;            //past clock phase
   
   //Initialization
   initial
     begin
        //Inputs
        assume(~clk_i);                                   //start out in high 
        assume(async_rst_i);                              //start out in reset
        assume(sync_rst_i);                               //start out in reset
        //Output
        gated_clk_o   <= 1'b0;                            //gate clock  
	//Internal state
        clk_reg       = 1'b0;                            //clock state
	por_cnt       = 2'b11;                           //start-up delay
     end // initial begin
   
   //Ungated clock input
   always @($global_clock)
     begin
        //Input
        assume(clk_i === clk_reg);                        //constraint clk_i
 	//Internal state
	clk_reg       <= ~clk_reg;                        //toggle clock
     end   
   
   //Gated clock output
   always @($global_clock)
     begin
	if (sync_i)
	  gated_clk_o <= ~clk_reg;                       //toggle gated clock
	else
	  gated_clk_o <= 1'b0;                           //keep gated clock stable
     end
   
   //Reset inputs	
   always @($global_clock)
     begin
	//Asynchronous reset
	if (!$rose(gated_clk_o) & async_rst_i)           //synchronous deassert
	  assume($stable(async_rst_i));

	//Synchronous reset
	if (!$rose(gated_clk_o))                         //synchronous assert and deassert
	  assume($stable(sync_rst_i));

	//Start-up delay
	if (por_cnt)
	  begin
             assume(async_rst_i);                        //start out in reset
             assume(sync_rst_i);                         //start out in reset
	     por_cnt <= por_cnt - 1;                     //decrement delay count
	  end
	
     end // always @ ($global_clock)
   
endmodule // wb_syscon
