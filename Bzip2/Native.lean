import Bzip2.ByteCodec
import Bzip2.Library

/-!
# Bzip2.Native

Executable byte-oriented API layer.

This module gathers the native `ByteArray` bridge (`Bzip2.ByteCodec`) and the
public in-memory / file API (`Bzip2.Library`). It is the main operational layer
used by tests and clients today.
-/
