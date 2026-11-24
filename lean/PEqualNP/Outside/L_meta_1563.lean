import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1563

def lineZero : Finset (Fin 13) := {0, 1, 3, 9}

def base : Finset (Fin 13 → Bool) :=
  Finset.univ.filter fun x => x 0 = true ∨ x 1 = true

def extras : Finset (Fin 13 → Bool) :=
  {fun v => decide (v ∉ lineZero), fun v => decide (v ∉ lineZero ∨ v = 3),
   fun v => decide (v ∉ lineZero ∨ v = 9), fun v => decide (v ∉ lineZero ∨ v = 3 ∨ v = 9)}

lemma base_card : base.card = 6144 := by
  let choices (v : Fin 13) : Finset Bool :=
    if v = 0 ∨ v = 1 then {false} else Finset.univ
  have hcompl : baseᶜ = Fintype.piFinset choices := by
    ext x
    simp only [Finset.mem_compl, base, Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset]
    constructor
    · intro h v
      by_cases hv : v = 0 ∨ v = 1
      · rcases hv with rfl | rfl <;> simp_all [choices]
      · simp [choices, hv]
    · intro h
      have h0 := h 0
      have h1 := h 1
      simp [choices] at h0 h1
      simp [h0, h1]
  have hcount : baseᶜ.card = 2048 := by
    rw [hcompl, Fintype.card_piFinset]
    decide
  have htotal := Finset.card_add_card_compl base
  rw [hcount] at htotal
  norm_num [Fintype.card_pi] at htotal
  omega

lemma classify (x : Fin 13 → Bool) :
    (x 0 = true ∨ x 1 = true ∨ ∀ v, v ∉ lineZero → x v = true) ↔ x ∈ base ∪ extras := by
  simp only [Finset.mem_union, base, Finset.mem_filter, Finset.mem_univ, true_and,
    extras, Finset.mem_insert, Finset.mem_singleton, or_assoc]
  by_cases h0 : x 0 = true
  · simp [h0]
  by_cases h1 : x 1 = true
  · simp [h1]
  simp only [h0, h1, reduceCtorEq, false_or]
  constructor
  · intro h
    have hz : x 0 = false := by simpa using h0
    have ho : x 1 = false := by simpa using h1
    cases h3 : x 3 <;> cases h9 : x 9
    case' false.false => left; funext v
    case' false.true => right; right; left; funext v
    case' true.false => right; left; funext v
    case' true.true => right; right; right; funext v
    all_goals
      by_cases hv : v ∈ lineZero
      · simp only [lineZero, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl <;> simp [hz, ho, h3, h9, lineZero]
      · simp [hv, h v hv]
  · rintro (rfl | rfl | rfl | rfl) <;> intro v hv <;> simp [hv]

lemma extra_card : extras.card = 4 := by decide

lemma disjoint_parts : Disjoint base extras := by
  rw [Finset.disjoint_left]
  intro x hx he
  have hb : x 0 = true ∨ x 1 = true := (Finset.mem_filter.mp hx).2
  simp only [extras, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;> revert hb <;> decide

end PEqualNP.Outside.L_meta_1563

open PEqualNP.Outside.L_meta_1563

theorem PEqualNP.Outside.L_meta_1563 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x y : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → (∀ v : Fin 13, x v = true → y v = true) → (y 0 = true ∨ y 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → y v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true))).card = 6148 ∧
    (∀ t : Fin 13, ((fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨ (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 ∧
    (∀ x : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) ↔ (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3 ∨ v = 9)))) := by
  intro L hL
  have hzero : L 0 = lineZero := hL 0
  refine ⟨?_, ?_, ?_, base_card, ?_⟩
  · intro x y hx hxy
    rcases hx with h | h | h
    · exact Or.inl (hxy 0 h)
    · exact Or.inr (Or.inl (hxy 1 h))
    · exact Or.inr (Or.inr (fun v hv => hxy v (h v hv)))
  · rw [hzero]
    have hs : (Finset.univ.filter (fun x : Fin 13 → Bool =>
        x 0 = true ∨ x 1 = true ∨ ∀ v, v ∉ lineZero → x v = true)) = base ∪ extras := by
      ext x
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using classify x
    rw [hs, Finset.card_union_of_disjoint disjoint_parts, base_card, extra_card]
  · have heq : L = fun t : Fin 13 => {t, t + 1, t + 3, t + 9} := funext hL
    subst L
    decide
  · rw [hzero]
    intro x
    simpa only [Finset.mem_union, base, Finset.mem_filter, Finset.mem_univ, true_and,
      extras, Finset.mem_insert, Finset.mem_singleton, or_assoc] using classify x
