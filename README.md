DFA.fs:
computes reaching definition and liveness analysis sets in order to aid optimization; provides functions for use by Optimize.fs

Optimize.fs:
optimizes the IR code generated by Translate.fs

Translate.fs:
translates a program AST that was generated from C into IR code