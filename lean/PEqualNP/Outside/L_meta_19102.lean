import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_19102 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (7935 : ℕ).testBit (4 * u.val + v.val)) C) := by
  let C : Circuit := ⟨[⟨.not, [4]⟩, ⟨.and, [2, 4]⟩, ⟨.and, [3, 8]⟩,
    ⟨.or, [9, 10]⟩, ⟨.not, [11]⟩], 12⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
