import BulksketchBridge.FrobeniusTableSpec

namespace BulksketchBridge.FrobeniusTable

open Aeneas.Std BulksketchProofs.Field.Period

def LookupRefines : Prop :=
  ∀ (word : U64) (power : U32),
    bulksketch.field.frobenius.lookup word power =
      Result.ok (if power.val ∈ powers then some (⟨iterateSquare power.val word.bv⟩ : U64)
        else none)

def InverseLookupRefines : Prop :=
  ∀ word : U64, bulksketch.field.frobenius.inverse21 word =
    Result.ok (⟨iterateSquare 21 word.bv⟩ : U64)

def StaticTablesRefine : Prop :=
  ∃ result : Tables, bulksketch.field.frobenius.TABLES = .ok result ∧
    ∀ index, index < 9 → Matches (powerAt index) (mapAt result index)

def StaticInverseTableRefines : Prop :=
  ∃ table : Map, bulksketch.field.frobenius.inverse21.TABLE = .ok table ∧ Matches 21 table

end BulksketchBridge.FrobeniusTable
