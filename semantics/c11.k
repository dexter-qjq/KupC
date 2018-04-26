require "language/execution/execution.k"
require "language/execution/ltlmc.k"
require "language/common/common.k"
require "library/library.k"
require "builtins/model-checker.k"

module C11-SYNTAX  
     imports MODEL-CHECKER-HOOKS
     imports LTL-HOOKS
     imports C-LTLMC-SYNTAX
endmodule

module C11
     imports C11-SYNTAX
     imports C-EXECUTION
     imports C-COMMON
     imports C-LIBRARY
     imports C-LTLMC

endmodule
