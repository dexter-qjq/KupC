require "language/execution2/execution.k"
require "language/execution2/ltlmc.k"
require "language/common/common.k"
require "library/library.k"
require "builtins/model-checker.k"

module C11-NON-SYNTAX  
     imports MODEL-CHECKER-HOOKS
     imports LTL-HOOKS
     imports C-LTLMC-SYNTAX
endmodule

module C11-NON
     imports C11-NON-SYNTAX
     imports C-EXECUTION
     imports C-COMMON
     imports C-LIBRARY
     imports C-LTLMC

endmodule
