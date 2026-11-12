import BulksketchBridge.FrobeniusLookupChallenges
import BulksketchBridge.FrobeniusLookupLoop
import BulksketchBridge.FrobeniusTables
import BulksketchBridge.FrobeniusInverseTable

namespace BulksketchBridge.FrobeniusTable

theorem static_tables_refine : StaticTablesRefine := by
  obtain ⟨tables, normal, cells⟩ := FrobeniusTables.tables_refines
  exact ⟨tables, by rw [bulksketch.field.frobenius.TABLES, normal], cells⟩

theorem static_inverse_table_refines : StaticInverseTableRefines := by
  obtain ⟨table, normal, cells⟩ := FrobeniusInverseTable.inverse21_table_refines
  exact ⟨table, by rw [bulksketch.field.frobenius.inverse21.TABLE, normal], cells⟩

theorem lookup_refines : LookupRefines := lookup_of_tables FrobeniusTables.tables_refines

theorem inverse21_refines : InverseLookupRefines :=
  inverse21_of_table FrobeniusInverseTable.inverse21_table_refines

end BulksketchBridge.FrobeniusTable
