import Arithmetic.FrobeniusTablesGenerated
import BulksketchProofs.Field.Period

namespace BulksketchBridge.FrobeniusTable

open Aeneas.Std BulksketchProofs.Field.Period

abbrev Row := Array U64 16#usize
abbrev Map := Array Row 16#usize
abbrev Tables := Array Map 9#usize

def powers : List Nat := [1, 2, 3, 4, 5, 6, 7, 15, 31]
def powerAt (index : Nat) : Nat := powers[index]?.getD 0

def cell (power row value : Nat) : BitVec 64 :=
  iterateSquare power ((BitVec.ofNat 64 value) <<< (4 * row))

def mapAt (tables : Tables) (index : Nat) : Map := tables[index]!
def cellAt (table : Map) (row value : Nat) : BitVec 64 := ((table[row]!)[value]!).bv

def Matches (power : Nat) (table : Map) : Prop :=
  ∀ row value, row < 16 → value < 16 → cellAt table row value = cell power row value

def TablesRefine : Prop :=
  ∃ result : Tables, bulksketch.field.frobenius.tables = .ok result ∧
    ∀ index, index < 9 → Matches (powerAt index) (mapAt result index)

def InverseTableRefines : Prop :=
  ∃ table : Map, bulksketch.field.frobenius.inverse21_table = .ok table ∧ Matches 21 table

end BulksketchBridge.FrobeniusTable
