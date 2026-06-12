import Bzip2.CLI

def main (args : List String) : IO UInt32 :=
  BZip2.CLI.run args
