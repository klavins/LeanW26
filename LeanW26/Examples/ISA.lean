--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

--import Mathlib

namespace LeanW26

--notdone

/-
Instruction Set Architectures
===
-/

inductive Opcode
  | NOP | LDA | ADD | SUB | STA | LDI | JMP | JC | JZ | OUT | HLT
  deriving DecidableEq

open Opcode

def decode (b : BitVec 4) : Opcode :=
  match b.toFin with
  | 0x1 => LDA | 0x2 => ADD | 0x3 => SUB
  | 0x4 => STA | 0x5 => LDI | 0x6 => JMP
  | 0x7 => JC | 0x8 => JZ | 0xE => OUT
  | 0xF => HLT
  | _ => NOP

structure State where
  pc : BitVec 4
  A : BitVec 8
  B : BitVec 8
  zf : Bool
  cf : Bool
  output : BitVec 8
  memory : Vector (BitVec 8) 16
  running : Bool

def add (x y : BitVec 8) : BitVec 8 × Bool :=
  let res : BitVec 8  := x + y
  let carry : Bool  := x.toNat + y.toNat > 255
  (res, carry)

#eval add 0b0100 0b11111100

def sub (x y : BitVec 8) : BitVec 8 × Bool :=
  let res : BitVec 8  :=  x + (~~~ y) + (1#8)
  let carry : Bool := x.toNat ≥ y.toNat
  (res, carry)

def Step (state : State) : State:=
  if state.running then
    let pc := state.pc
    let i := state.memory[pc.toFin]
    let opcode := i.extractLsb 7 4
    let arg := i.extractLsb 3 0
    match decode opcode with
    | LDA => { state with
        A := state.memory[arg.toFin]
        pc := pc + 1
      }
    | ADD =>
        let b := state.memory[arg.toFin]
        let ⟨ sum, carry ⟩  := add state.A b
        { state with
          B := b
          A := sum
          zf := sum.toFin = 0
          cf := carry
          pc := pc + 1
        }
    | SUB =>
       let b := state.memory[arg.toFin]
       let ⟨ diff, carry ⟩ := sub state.A b
       { state with
          B := b
          A := diff
          zf := diff.toFin = 0
          cf := carry
          pc := pc + 1
          }
    | STA => { state with
        memory := state.memory.set arg.toFin state.A
        pc := pc + 1
      }
    | LDI => { state with
        A := BitVec.ofNat 8 arg.toFin
        pc := pc + 1
      }
    | JMP => {state with pc := arg }
    | JZ  => { state with  pc := if state.zf then arg else pc + 1  }
    | JC  => { state with pc := if state.cf then arg else pc + 1 }
    | OUT => { state with
      output := state.A
      pc := pc + 1
    }
    | HLT => { state with running := false }
    | _ => { state with pc := pc + 1 }
  else
    state

end LeanW26


def X : Set Nat := { n | n > 4 }
