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
    input wire                             clk_i,            //module clock
    input wire                             async_rst_i,      //asynchronous reset
    input wire                             sync_rst_i);      //synchronous reset

   //Internal signals
   //================
   reg                                     prev_clk_i;       //previous clock phase

   //Reset condition
   //===============
   initial
     begin
        prev_clk_i = 1'b1;                                   //initialize prev. clock state
        assume (~clk_i);                                     //module clock
        assume (async_rst_i);                                //asynchronous reset
        assume (sync_rst_i);                                 //synchronous reset
        @($global_clock);
        assume (async_rst_i);                                //asynchronous reset
        assume (sync_rst_i);                                 //synchronous reset
     end

   //Expect free-running clock
   //=========================
   always @($global_clock)
     begin
        assume (clk_i ^ prev_clk_i);
        prev_clk_i <= clk_i;
     end

endmodule // wb_syscon
