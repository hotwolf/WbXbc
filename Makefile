###############################################################################
# WbXbc - Makefile                                                            #
###############################################################################
#    Copyright 2018 Dirk Heisswolf                                            #
#    This file is part of the WbXbc project.                                  #
#                                                                             #
#    WbXbc is free software: you can redistribute it and/or modify            #
#    it under the terms of the GNU General Public License as published by     #
#    the Free Software Foundation, either version 3 of the License, or        #
#    (at your option) any later version.                                      #
#                                                                             #
#    WbXbc is distributed in the hope that it will be useful,                 #
#    but WITHOUT ANY WARRANTY; without even the implied warranty of           #
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            #
#    GNU General Public License for more details.                             #
#                                                                             #
#    You should have received a copy of the GNU General Public License        #
#    along with WbXbc.  If not, see <http://www.gnu.org/licenses/>.           #
###############################################################################
# Description:                                                                #
#    This is the project makefile to run all verifcation and documentation    #
#    tasks. A description of all supported rules is given in the help text.   #
#                                                                             #
###############################################################################
# Version History:                                                            #
#   October 17, 2018                                                          #
#      - Initial release                                                      #
###############################################################################

#Directories
REPO_DIR    := .
#REPO_DIR   := $(CURDIR)
RTL_DIR     := $(REPO_DIR)/rtl/verilog
BENCH_DIR   := $(REPO_DIR)/bench/verilog
SBY_DIR     := $(REPO_DIR)/tools/SymbiYosis
SBY_SRC_DIR := $(REPO_DIR)/tools/SymbiYosis/src
SBY_WRK_DIR := $(REPO_DIR)/tools/SymbiYosis/run
DOC_DIR     := $(REPO_DIR)/doc
DOC_SRC_DIR := $(DOC_DIR)/src

#List of modules and their supported configurations <module>.<configuration>
MODCONFS := $(sort	WbXbc_accelerator.default \
			WbXbc_accelerator.reg_itr \
			WbXbc_address_decoder.default \
			WbXbc_arbiter.default \
			WbXbc_decelerator.default \
			WbXbc_decelerator.reg_itr \
			WbXbc_decelerator.reg_tgt \
			WbXbc_decelerator.reg_itrtgt \
			WbXbc_distributor.default \
			WbXbc_error_generator.default \
			WbXbc_expander.default \
			WbXbc_expander.little_endian \
			WbXbc_pipeliner.default \
			WbXbc_reducer.default \
			WbXbc_reducer.little_endian \
			WbXbc_splitter.default \
			WbXbc_standardizer.default \
			WbXbc_xbar.default)

MODS  := $(sort $(foreach mod,$(MODCONFS),$(firstword $(subst ., ,$(mod)))))
CONFS := $(sort $(foreach mod,$(MODCONFS),$(lastword  $(subst ., ,$(mod)))))

.SECONDEXPANSION:

#############
# Help text #
#############
help:
	@echo "This makefile supports the following targets:"
	@echo " "
	@echo "lint:                            Lint all modules in all supported configurations"
	@echo "lint.<module>.<configuration>:   Lint a module in one particular configuration"
	@echo "lint.<module>:                   Lint a module in all supported cinfigurations"
	@echo "lint.<configuration>:            Lint all modules which support the given configuration"
	@echo "lint.clean:                      Clean up lint targets"
	@echo " "
	@echo "verify:                          Verify all modules in all supported configurations"
	@echo "verify.<module>.<configuration>: Verify a module in one particular configuration"
	@echo "verify.<module>:                 Verify a module in all supported cinfigurations"
	@echo "verify.<configuration>:          Verify all modules which support the given configuration"
	@echo "verify.clean:                    Clean up verify targets"
	@echo " "
	@echo "bmc:                             Generate bounded proofs for all modules in all support configurations"
	@echo "bmc.<module>.<configuration>:    Generate bounded proofs for a module in one particular configuration"
	@echo "bmc.<module>:                    Generate bounded proofs for a module in all supported cinfigurations"
	@echo "bmc.<configuration>:             Generate bounded proofs for all modules which support the given configuration"
	@echo "bmc.clean:                       Clean up bounded proof targets"
	@echo " "
	@echo "prove:                           Generate unboundeds proof for all modules in all supported configurations"
	@echo "prove.<module>.<configuration>:  Generate unboundeds proof for a module in one particular configuration"
	@echo "prove.<module>:                  Generate unboundeds proof for a module in all supported cinfigurations"
	@echo "prove.<configuration>:           Generate unboundeds proof for all modules which support the given configuration"
	@echo "prove.clean:                     Clean up unbounded proof targets"
	@echo " "
	@echo "live:                            Prove liveness of all modules in all supported configurations"
	@echo "live.<module>.<configuration>:   Prove liveness of a module in one particular configuration"
	@echo "live.<module>:                   Prove liveness of a module in all supported cinfigurations"
	@echo "live.<configuration>:            Prove liveness of all modules which support the given configuration"
	@echo "live.clean:                      Clean up liveness targets"
	@echo " "
	@echo "cover:                           Generate cover traces for all modules in all supported configurations"
	@echo "cover.<module>.<configuration>:  Generate cover traces for a module in one particular configuration"
	@echo "cover.<module>:                  Generate cover traces for a module in all supported cinfigurations"
	@echo "cover.<configuration>:           Generate cover traces for all modules which support the given configuration"
	@echo "cover.clean:                     Clean up cover targets"
	@echo " "
	@echo "clean:                           Clean up all targets"
	@echo " "
	@echo "doc:                             Build the user manual"

###########
# Linting #
###########
LINT_MODCONFS := $(MODCONFS:%=lint.%)
LINT_MODS     := $(MODS:%=lint.%)
LINT_CONFS    := $(CONFS:%=lint.%)

$(LINT_MODCONFS):
	$(eval mod     := $(word 2,$(subst ., ,$@)))
	$(eval conf    := $(lastword $(subst ., ,$@)))
	$(eval confdef := CONF_$(shell echo $(conf) | tr '[:lower:]' '[:upper:]'))
	@echo "...Linting $(mod) in $(conf) configuration"
	@iverilog -t null -D $(confdef) -s ftb_$(mod) -y $(RTL_DIR) $(BENCH_DIR)/ftb_$(mod).sv $(RTL_DIR)/$(mod).v  
	@yosys -q -p "read_verilog -sv -D $(confdef) -I $(RTL_DIR) $(BENCH_DIR)/ftb_$(mod).sv $(RTL_DIR)/$(mod).v"

$(LINT_MODS): $$(filter $$@.%,$(LINT_MODCONFS))

$(LINT_CONFS): $$(filter lint.%.$$(lastword $$(subst ., ,$$@)),$(LINT_MODCONFS))

lint:	$(LINT_MODCONFS) 

lint.clean:

################################
# Complete formal verification #
################################
VERIFY_MODCONFS := $(MODCONFS:%=verify.%)
VERIFY_MODS     := $(MODS:%=verify.%)
VERIFY_CONFS    := $(CONFS:%=verify.%)

$(VERIFY_MODCONFS): $$(subst verify.,prove.,$$@) $$(subst verify.,cover.,$$@) $$(subst verify.,live.,$$@)

$(VERIFY_MODS): $$(filter $$@.%,$(VERIFY_MODCONFS))

$(VERIFY_CONFS): $$(filter verify.%.$$(lastword $$(subst ., ,$$@)),$(VERIFY_MODCONFS))

verify:	$(VERIFY_MODCONFS) 

verify.clean: prove.clean cover.clean live.clean

##################
# Bounded proofs #
##################
BMC_MODCONFS := $(MODCONFS:%=bmc.%)
BMC_MODS     := $(MODS:%=bmc.%)
BMC_CONFS    := $(CONFS:%=bmc.%)

$(BMC_MODCONFS):
	$(eval mod     := $(word 2,$(subst ., ,$@)))
	$(eval conf    := $(lastword $(subst ., ,$@)))
	@echo "...Generating bounded proofs for $(mod) in $(conf) configuration"
	@ln -sf $@ $(SBY_WRK_DIR)/bmc.latest
	@sby -f -d $(SBY_WRK_DIR)/$@ $(SBY_SRC_DIR)/$(mod).sby bmc.$(conf)

$(BMC_MODS): $$(filter $$@.%,$(BMC_MODCONFS))

$(BMC_CONFS): $$(filter bmc.%.$$(lastword $$(subst ., ,$$@)),$(BMC_MODCONFS))

bmc: $(BMC_MODCONFS) 

bmc.clean:
	@echo "...Cleaning up bounded proof targets"
	@rm -rf $(BMC_MODCONFS:%=$(SBY_WRK_DIR)/%) $(SBY_WRK_DIR)/bmc.latest 

###################
# Unounded proofs #
###################
PROVE_MODCONFS := $(MODCONFS:%=prove.%)
PROVE_MODS     := $(MODS:%=prove.%)
PROVE_CONFS    := $(CONFS:%=prove.%)

$(PROVE_MODCONFS):
	$(eval mod     := $(word 2,$(subst ., ,$@)))
	$(eval conf    := $(lastword $(subst ., ,$@)))
	@echo "...Generating unbounded proofs $(mod) in $(conf) configuration"
	@ln -sf $@ $(SBY_WRK_DIR)/prove.latest
	@sby -f -d $(SBY_WRK_DIR)/$@ $(SBY_SRC_DIR)/$(mod).sby prove.$(conf)

$(PROVE_MODS): $$(filter $$@.%,$(PROVE_MODCONFS))

$(PROVE_CONFS): $$(filter prove.%.$$(lastword $$(subst ., ,$$@)),$(PROVE_MODCONFS))

prove:	$(PROVE_MODCONFS) 

prove.clean:
	@echo "...Cleaning up unbounded proof targets"
	@rm -rf $(BMC_MODCONFS:%=$(SBY_WRK_DIR)/%) $(SBY_WRK_DIR)/prove.latest 

############
# Liveness #
############
LIVE_MODCONFS := $(MODCONFS:%=live.%)
LIVE_MODS     := $(MODS:%=live.%)
LIVE_CONFS    := $(CONFS:%=live.%)

$(LIVE_MODCONFS):
	$(eval mod     := $(word 2,$(subst ., ,$@)))
	$(eval conf    := $(lastword $(subst ., ,$@)))
	@echo "...Proving liveness of $(mod) in $(conf) configuration"
	@ln -sf $@ $(SBY_WRK_DIR)/live.latest
	@sby -f -d $(SBY_WRK_DIR)/$@ $(SBY_SRC_DIR)/$(mod).sby live.$(conf)

$(LIVE_MODS): $$(filter $$@.%,$(LIVE_MODCONFS))

$(LIVE_CONFS): $$(filter live.%.$$(lastword $$(subst ., ,$$@)),$(LIVE_MODCONFS))

live:	$(LIVE_MODCONFS) 

live.clean:
	@echo "...Cleaning up liveness targets"
	@rm -rf $(BMC_MODCONFS:%=$(SBY_WRK_DIR)/%) $(SBY_WRK_DIR)/prove.latest 

################
# Cover traces #
################
COVER_MODCONFS := $(MODCONFS:%=cover.%)
COVER_MODS     := $(MODS:%=cover.%)
COVER_CONFS    := $(CONFS:%=cover.%)

$(COVER_MODCONFS):
	$(eval mod     := $(word 2,$(subst ., ,$@)))
	$(eval conf    := $(lastword $(subst ., ,$@)))
	@echo "...Generating cover traces for $(mod) in $(conf) configuration"
	@ln -sf $@ $(SBY_WRK_DIR)/cover.latest
	@sby -f -d $(SBY_WRK_DIR)/$@ $(SBY_SRC_DIR)/$(mod).sby cover.$(conf)

$(COVER_MODS): $$(filter $$@.%,$(COVER_MODCONFS))

$(COVER_CONFS): $$(filter cover.%.$$(lastword $$(subst ., ,$$@)),$(COVER_MODCONFS))

cover:	$(COVER_MODCONFS) 

cover.clean:
	@echo "...Cleaning up cover targets"
	@rm -rf $(BMC_MODCONFS:%=$(SBY_WRK_DIR)/%) $(SBY_WRK_DIR)/cover.latest 

#################
# Documentation #
#################

doc:
	$(MAKE) -C $(DOC_SRC_DIR)

#latex -interaction=nonstopmode %.tex|bibtex %.aux|latex -interaction=nonstopmode %.tex|latex -interaction=nonstopmode %.tex|xdvi %.dvi
#pdflatex -synctex=1 -interaction=nonstopmode %.tex

############
# Clean up #
############

clean:	lint.clean bmc.clean prove.clean cover.clean

####################
# General targetds #
####################

.PHONY:	help \
	$(LINT_MODCONFS)   $(LINT_MODS)   $(LINT_CONFS)   lint   lint.clean \
	$(VERIFY_MODCONFS) $(VERIFY_MODS) $(VERIFY_CONFS) verify verify.clean \
	$(BMC_MODCONFS)    $(BMC_MODS)    $(BMC_CONFS)    bmc    bmc.clean \
	$(PROVE_MODCONFS)  $(PROVE_MODS)  $(PROVE_CONFS)  prove  prove.clean \
	$(LIVE_MODCONFS)   $(LIVE_MODS)   $(LIVE_CONFS)   live   live.clean \
	$(COVER_MODCONFS)  $(COVER_MODS)  $(COVER_CONFS)  cover  cover.clean \
	doc \
	clean
