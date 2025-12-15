
import VersoManual
open Verso.Genre Manual


namespace LeanW26.Docs

inductive MyInline | note : String → MyInline
inductive MyBlock  | callout : String → MyBlock

end LeanW26.Docs
