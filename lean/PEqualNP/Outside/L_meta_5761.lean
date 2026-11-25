import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5761_aux

section Basis

-- Circuit evaluation and frontier counting adapt L-meta-3706 and willakone’s L-meta-1491.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
namespace S90

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

end S90
lemma orIn_iff_reach {n : ℕ} {C : Circuit} (p : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C p ↔ Relation.ReflTransGen (S90.OrStep n C) p u.val :=
  ⟨S90.mem_orIn_reach u, S90.reach_mem_orIn u⟩

lemma orIn_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [orIn_iff_reach] at ha hb
  have h1 : ∀ c : Fin n, Relation.ReflTransGen (S90.OrStep n C) w c.val → c.val = w := by
    intro c hc
    rcases Relation.ReflTransGen.cases_head hc with h | ⟨d, hd, _⟩
    · exact h.symm
    · obtain ⟨k, _, h3, _⟩ := hd
      omega
  exact Fin.ext ((h1 a ha).trans (h1 b hb).symm)

lemma orIn_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔ k < C.gates.length ∧
      (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧
        u ∈ PEqualNP.TopForm.orIn n C w := by
  rw [orIn_iff_reach]
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨d, hd, hr⟩
    · have := u.isLt
      omega
    · obtain ⟨k', hk', he, hop, hin, hlt⟩ := hd
      have hkk : k' = k := by omega
      subst hkk
      exact ⟨hk', hop, d, hin, hlt, (orIn_iff_reach d u).2 hr⟩
  · rintro ⟨hk, hop, w, hw, hlt, hu⟩
    exact Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hw, hlt⟩ ((orIn_iff_reach w u).1 hu)

open PEqualNP.MetaComplexity PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.CleanedNonEdge

noncomputable def frontier (n : ℕ) (C : Circuit) (op : GateOp) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter
    (fun j => (gateAt C j).op = op ∧ OrReaches n C C.output j)

lemma mem_frontier {n : ℕ} {C : Circuit} {op : GateOp} {j : ℕ} :
    j ∈ frontier n C op ↔
      j < C.gates.length ∧ (gateAt C j).op = op ∧ OrReaches n C C.output j := by
  classical
  simp [frontier]

lemma frontier_count {n : ℕ} (C : Circuit) (hModel : IsAO2 n C) :
    (frontier n C GateOp.and).card ≤ (frontier n C GateOp.or).card + 1 := by
  classical
  let A := frontier n C GateOp.and
  let O := frontier n C GateOp.or
  have hdisj : Disjoint A O := by
    refine Finset.disjoint_left.2 ?_
    intro j hjA hjO
    have h := (mem_frontier.1 hjA).2.1.symm.trans (mem_frontier.1 hjO).2.1
    cases h
  let inputs := O.biUnion (fun i => (gateAt C i).inputs.toFinset)
  have hsub : (A ∪ O).image (fun j => n + j) ⊆ insert C.output inputs := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
    have hr : OrReaches n C C.output j := by
      rcases Finset.mem_union.1 hj with hj | hj
      · exact (mem_frontier.1 hj).2.2
      · exact (mem_frontier.1 hj).2.2
    have hp := (S90.orReaches_reach j C.output hr).1
    rcases Relation.ReflTransGen.cases_tail hp with he | ⟨w, hw, hstep⟩
    · rw [← he]
      exact Finset.mem_insert_self _ _
    · obtain ⟨i, hi, rfl, hop, hins, _⟩ := hstep
      have hiO : i ∈ O := mem_frontier.2
        ⟨hi, hop, S90.reach_orReaches hw i rfl hi⟩
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2
        ⟨i, hiO, List.mem_toFinset.2 hins⟩)
  have hinput : inputs.card ≤ O.card * 2 := by
    apply Finset.card_biUnion_le_card_mul
    intro k hk
    have hklen := (mem_frontier.1 hk).1
    exact (List.toFinset_card_le _).trans_eq (hModel.2.2 _ (S90.gateAt_mem hklen))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h),
    Finset.card_union_of_disjoint hdisj] at hc
  have hi := Finset.card_insert_le C.output inputs
  change A.card ≤ O.card + 1
  omega

lemma frontier_orIn_empty {n : ℕ} {C : Circuit} (hsingle : ∀ v : Fin n,
    circuitFun n C (fun u => decide (u = v)) = false) {j : ℕ}
    (hj : j ∈ frontier n C GateOp.or) : orIn n C (n + j) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  have hjReach := (S90.orReaches_reach j C.output (mem_frontier.1 hj).2.2).1
  have hraw := S90.mem_orIn_reach v hv
  have htrue : circuitFun n C (fun u => decide (u = v)) = true :=
    S90.reach_var_val _ _ v (hjReach.trans hraw) (by simp)
  rw [hsingle v] at htrue
  cases htrue

end Basis

section Packing

variable {n m : ℕ}
abbrev V (n m : ℕ) := Fin n ⊕ Fin m
abbrev Edge (n m : ℕ) := Fin n × Fin m

def adj (E : Finset (Edge n m)) : V n m → V n m → Prop
  | .inl p, .inr l => (p,l) ∈ E
  | .inr l, .inl p => (p,l) ∈ E
  | _, _ => False

theorem adj_symm {E : Finset (Edge n m)} {v w : V n m} (h : adj E v w) : adj E w v := by
  cases v <;> cases w <;> exact h

abbrev SquareFree (E : Finset (Edge n m)) := ∀ p q l r, p ≠ q → l ≠ r →
  ¬ ((p,l) ∈ E ∧ (p,r) ∈ E ∧ (q,l) ∈ E ∧ (q,r) ∈ E)

theorem unique_common {E : Finset (Edge n m)} (sq : SquareFree E)
    {a b x y : V n m} (ha : adj E a x) (hb : adj E a y)
    (hc : adj E b x) (hd : adj E b y) (hxy : x ≠ y) : a = b := by
  cases a <;> cases b <;> cases x <;> cases y <;> simp_all [adj] <;>
    by_contra h <;> apply sq _ _ _ _ (by assumption) (by assumption) <;> tauto

def starEdges (c : V n m) (S : Finset (V n m)) : Finset (Edge n m) :=
  match c with
  | .inl p => S.toRight.image (fun l => (p,l))
  | .inr l => S.toLeft.image (fun p => (p,l))

theorem star_card (c : V n m) (S : Finset (V n m)) : (starEdges c S).card ≤ S.card := by
  cases c with
  | inl p => exact Finset.card_image_le.trans S.card_toRight_le
  | inr l => exact Finset.card_image_le.trans S.card_toLeft_le

theorem star_union (c : V n m) (S T : Finset (V n m)) :
    starEdges c (S ∪ T) = starEdges c S ∪ starEdges c T := by
  cases c <;> simp [starEdges, Finset.toLeft_union, Finset.toRight_union, Finset.image_union]

theorem star_mem {c : V n m} {S : Finset (V n m)} {e : Edge n m} :
    e ∈ starEdges c S ↔ (c = Sum.inl e.1 ∧ Sum.inr e.2 ∈ S) ∨
                          (c = Sum.inr e.2 ∧ Sum.inl e.1 ∈ S) := by
  rcases e with ⟨p,l⟩
  cases c <;> simp [starEdges, Prod.ext_iff, eq_comm, and_comm]

abbrev Fits (E : Finset (Edge n m)) (c : V n m) (S : Finset (V n m)) :=
  ∀ v ∈ S, adj E c v

noncomputable def edgesAt (E : Finset (Edge n m)) (c : V n m) (S : Finset (V n m)) :=
  open Classical in if Fits E c S then starEdges c S else ∅

theorem edges_split {E : Finset (Edge n m)} {c : V n m} {S T : Finset (V n m)}
    (h : Fits E c (S ∪ T)) :
    edgesAt E c (S ∪ T) = edgesAt E c S ∪ edgesAt E c T := by
  classical
  have hs : Fits E c S := fun v hv => h _ (Finset.mem_union_left _ hv)
  have ht : Fits E c T := fun v hv => h _ (Finset.mem_union_right _ hv)
  simp only [edgesAt,ite_eq_left h,ite_eq_left hs,ite_eq_left ht,star_union]

theorem big_owners {E : Finset (Edge n m)} (sq : SquareFree E)
    {c d : V n m} {S : Finset (V n m)} (hc : Fits E c S) (hd : Fits E d S)
    (big : 1 < S.card) : c = d := by
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp big
  exact unique_common sq (hc _ hx) (hc _ hy) (hd _ hx) (hd _ hy) hxy

theorem rectangle_small {E : Finset (Edge n m)} (sq : SquareFree E)
    {S T : Finset (V n m)} (all : ∀ u ∈ S, ∀ v ∈ T, adj E u v) :
    S.card ≤ 1 ∨ T.card ≤ 1 := by
  by_contra! h
  obtain ⟨x,hx,y,hy,ne⟩ := Finset.one_lt_card.mp h.1
  exact ne (big_owners sq (all _ hx) (all _ hy) h.2)

end Packing

section Circuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership
open Relation S90

abbrev Pure {N : ℕ} (C : Circuit) (U : Finset ℕ) :=
  ∀ w ∈ U, w < N ∨ ∃ j < C.size, w = N+j ∧ (gateAt C j).op = .or ∧
                                     ∀ u ∈ (gateAt C j).inputs, u ∈ U

theorem trace {N : ℕ} {C : Circuit} (ao : IsAO2 N C) (z : Fin N → Bool) (w : ℕ)
    (hv : val C (List.ofFn z) w = true) :
    (∃ u : Fin N, ReflTransGen (OrStep N C) w u.val ∧ z u = true) ∨
    ∃ j < C.size, (gateAt C j).op = .and ∧ ReflTransGen (OrStep N C) w (N+j) ∧
       val C (List.ofFn z) (N+j) = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hr : w < N
    · exact Or.inl ⟨⟨w,hr⟩,.refl,(val_ofFn C z ⟨w,hr⟩).symm.trans hv⟩
    obtain ⟨j,rfl⟩ : ∃ j, w = N+j := ⟨w-N, by omega⟩
    by_cases hj : j < C.gates.length
    · rcases ao.1 _ (gateAt_mem hj) with ha | ho
      · exact Or.inr ⟨j,hj,ha,.refl,hv⟩
      · obtain ⟨u,hu,lt,hv'⟩ := (val_or (n:=N) (by simp) hj ho).mp hv
        have step : OrStep N C (N+j) u := ⟨j,hj,rfl,ho,hu,lt⟩
        rcases ih u lt hv' with ⟨v,p,h⟩ | ⟨i,hi,op,p,h⟩
        · exact Or.inl ⟨v,.head step p,h⟩
        · exact Or.inr ⟨i,hi,op,.head step p,h⟩
    · rw [val_ge (n:=N) (by simp) (by omega)] at hv
      cases hv

theorem pure_on {N : ℕ} {C : Circuit} {U : Finset ℕ} (pure : Pure (N:=N) C U)
    (z : Fin N → Bool) {w : ℕ} (hw : w ∈ U) (hv : val C (List.ofFn z) w = true) :
    ∃ u ∈ orIn N C w, z u = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases pure w hw with hr | ⟨j,hj,rfl,op,parents⟩
    · exact ⟨⟨w,hr⟩,reach_mem_orIn _ .refl,(val_ofFn C z ⟨w,hr⟩).symm.trans hv⟩
    · obtain ⟨u,hu,lt,on⟩ := (val_or (n:=N) (by simp) hj op).mp hv
      obtain ⟨v,mem,on'⟩ := ih u lt (parents u hu) on
      exact ⟨v,reach_mem_orIn _ (.head ⟨j,hj,rfl,op,hu,lt⟩ (mem_orIn_reach v mem)),on'⟩

variable {n m : ℕ}
abbrev idx (v : V n m) : Fin (n+m) := finSumFinEquiv v
def support (C : Circuit) (w : ℕ) : Finset (V n m) :=
  (orIn (n+m) C w).map finSumFinEquiv.symm.toEmbedding
theorem support_iff {C : Circuit} {w : ℕ} {u : V n m} :
    u ∈ support C w ↔ idx u ∈ orIn (n+m) C w := by
  simp [support, idx]

abbrev Computes (E : Finset (Edge n m)) (C : Circuit) := ∀ z,
  circuitFun (n+m) C z = decide (∃ p l, (p,l) ∈ E ∧
    z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)

theorem pair_iff {E : Finset (Edge n m)} {C : Circuit} (hc : Computes E C) (u v : V n m) :
    circuitFun (n+m) C (pairInput (idx u) (idx v)) = true ↔ adj E u v := by
  rw [hc,decide_eq_true_eq]
  simp only [pairInput_true]
  have eqidx (a b : V n m) : idx a = idx b ↔ a=b := finSumFinEquiv.injective.eq_iff
  change (∃ p l, (p,l) ∈ E ∧ (idx (.inl p) = idx u ∨ idx (.inl p) = idx v) ∧
    (idx (.inr l) = idx u ∨ idx (.inr l) = idx v)) ↔ _
  simp only [eqidx]
  cases u <;> cases v <;> simp [adj]

theorem single_off {E : Finset (Edge n m)} {C : Circuit} (hc : Computes E C)
    (v : Fin (n+m)) : circuitFun (n+m) C (fun u => decide (u=v)) = false := by
  obtain ⟨w,rfl⟩ := finSumFinEquiv.surjective v
  have h := pair_iff hc w w
  have same : (fun u => decide (u=idx w)) = pairInput (idx w) (idx w) := by
    funext u
    simp [pairInput]
  rw [same,Bool.eq_false_iff]
  intro hh
  have bad := h.mp hh
  cases w <;> exact bad

theorem pair_inputs {N : ℕ} {C : Circuit} (ao : IsAO2 N C) {j : ℕ} (hj : j < C.size) :
    (gateAt C j).inputs = [opnd C j 0,opnd C j 1] := by
  obtain ⟨a,b,eq⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hj))
  simp [opnd,eq]

theorem cross_adj {E : Finset (Edge n m)} {C : Circuit} (ao : IsAO2 (n+m) C)
    (hc : Computes E C) {j : ℕ} (hj : j ∈ frontier (n+m) C .and)
    {u v : V n m} (hu : u ∈ support C (opnd C j 0)) (hv : v ∈ support C (opnd C j 1)) :
    adj E u v := by
  obtain ⟨hj',op,reach⟩ := mem_frontier.mp hj
  have inputs := pair_inputs ao hj'
  let z := pairInput (idx u) (idx v)
  apply (pair_iff hc u v).mp
  apply orStep_up (n:=n+m) (by simp) (orReaches_reach j _ reach).1
  apply (val_and (n:=n+m) (by simp) hj' op).mpr
  intro w hw
  refine ⟨ao.2.1 j hj' w hw,?_⟩
  rw [inputs,List.mem_pair] at hw
  rcases hw with rfl | rfl
  · exact reach_var_val z _ _ (mem_orIn_reach _ (support_iff.mp hu)) (pairInput_left _ _)
  · exact reach_var_val z _ _ (mem_orIn_reach _ (support_iff.mp hv)) (pairInput_right _ _)

end Circuit

section Roots

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership S90
variable {n m : ℕ}

abbrev Fan (C : Circuit) (j : ℕ) (s : Fin 2) : Finset (V n m) := support C (opnd C j s)

noncomputable def productive (n m : ℕ) (C : Circuit) :=
  (frontier (n+m) C .and).filter (fun j =>
    (Fan (n:=n) (m:=m) C j 0).Nonempty ∧ (Fan (n:=n) (m:=m) C j 1).Nonempty)

theorem extract {E : Finset (Edge n m)} {C : Circuit} {U : Finset ℕ}
    (ao : IsAO2 (n+m) C) (hc : Computes E C) (pure : Pure (N:=n+m) C U)
    (parents : ∀ j < C.size, (gateAt C j).op = .and → ∀ w ∈ (gateAt C j).inputs, w ∈ U)
    {p : Fin n} {l : Fin m} (edge : (p,l) ∈ E) :
    ∃ j ∈ productive n m C,
      (Sum.inl p ∈ Fan (n:=n) (m:=m) C j 0 ∧ Sum.inr l ∈ Fan (n:=n) (m:=m) C j 1) ∨
      (Sum.inr l ∈ Fan (n:=n) (m:=m) C j 0 ∧ Sum.inl p ∈ Fan (n:=n) (m:=m) C j 1) := by
  let u : V n m := .inl p
  let v : V n m := .inr l
  let z := pairInput (idx u) (idx v)
  have on : circuitFun (n+m) C z = true := (pair_iff hc u v).mpr edge
  rcases trace ao z C.output on with ⟨w,reach,_⟩ | ⟨j,hj,op,reach,hit⟩
  · have hs := single_off hc w
    have ht : circuitFun (n+m) C (fun i => decide (i = w)) = true :=
      reach_var_val _ _ w reach (by simp)
    rw [hs] at ht
    cases ht
  · have top : j ∈ frontier (n+m) C .and :=
      mem_frontier.mpr ⟨hj,op,reach_orReaches reach _ rfl hj⟩
    have ins := pair_inputs ao hj
    have hits (s : Fin 2) : ∃ x ∈ Fan (n:=n) (m:=m) C j s, x = u ∨ x = v := by
      have mem : opnd C j s ∈ (gateAt C j).inputs := by
        rw [ins]
        fin_cases s <;> simp
      obtain ⟨w,hw,active⟩ := pure_on pure z (parents _ hj op _ mem)
        (((val_and (n:=n+m) (by simp) hj op).mp hit _ mem).2)
      obtain ⟨x,rfl⟩ := finSumFinEquiv.surjective w
      have alt : idx x = idx u ∨ idx x = idx v := (pairInput_true _ _ _).mp active
      exact ⟨x,support_iff.mpr hw,alt.imp (fun h => finSumFinEquiv.injective h)
        (fun h => finSumFinEquiv.injective h)⟩
    obtain ⟨x,hx,eqx⟩ := hits 0
    obtain ⟨y,hy,eqy⟩ := hits 1
    refine ⟨j,Finset.mem_filter.mpr ⟨top,⟨x,hx⟩,⟨y,hy⟩⟩,?_⟩
    have ad := cross_adj ao hc top hx hy
    rcases eqx with h | h <;> subst x <;> rcases eqy with h | h <;> subst y
    · exact False.elim ad
    · exact Or.inl ⟨hx,hy⟩
    · exact Or.inr ⟨hx,hy⟩
    · exact False.elim ad

theorem assign {E : Finset (Edge n m)} {C : Circuit}
    (ao : IsAO2 (n+m) C) (hc : Computes E C) (sq : SquareFree E)
    (j : {j // j ∈ productive n m C}) :
    ∃ (c : V n m) (r : ℕ), r < n+m+C.size ∧ Fits E c (support C r) ∧
      ∀ u ∈ Fan (n:=n) (m:=m) C j 0, ∀ v ∈ Fan (n:=n) (m:=m) C j 1,
        (c = u ∧ v ∈ support C r) ∨ (c = v ∧ u ∈ support C r) := by
  obtain ⟨ha,h0,h1⟩ := Finset.mem_filter.mp j.property
  have hj := (mem_frontier.mp ha).1
  have adjall : ∀ u ∈ Fan (n:=n) (m:=m) C j 0, ∀ v ∈ Fan (n:=n) (m:=m) C j 1, adj E u v :=
    fun _ hu _ hv => cross_adj ao hc ha hu hv
  have lt (s : Fin 2) : opnd C j s < n+m+C.size := by
    have ins := pair_inputs ao hj
    have mem : opnd C j s ∈ (gateAt C j).inputs := by rw [ins]; fin_cases s <;> simp
    have hb := ao.2.1 _ hj _ mem
    change j.val < C.size at hj
    omega
  rcases rectangle_small sq adjall with hs | hs
  · obtain ⟨c,hc'⟩ := h0
    exact ⟨c,opnd C j 1,lt 1,adjall _ hc', fun _ hu _ hv =>
      Or.inl ⟨Finset.card_le_one.mp hs _ hc' _ hu,hv⟩⟩
  · obtain ⟨c,hc'⟩ := h1
    exact ⟨c,opnd C j 0,lt 0,(fun _ hu => adj_symm (adjall _ hu _ hc')), fun _ hu _ hv =>
      Or.inr ⟨Finset.card_le_one.mp hs _ hc' _ hv,hu⟩⟩

end Roots

section Wires

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm
variable {n m : ℕ} {E : Finset (Edge n m)} {C : Circuit}

noncomputable def lower (E : Finset (Edge n m)) (C : Circuit) (c : V n m) : Finset ℕ := by
  classical
  exact (Finset.range (n+m+C.size)).filter (fun w =>
    Fits E c (support C w) ∧ 1 < (support (n:=n) (m:=m) C w).card)

theorem owned_or {c : V n m} {w : ℕ} (hw : w ∈ lower E C c) :
    ∃ j < C.size, w = n+m+j ∧ (gateAt C j).op = .or := by
  classical
  obtain ⟨hw',_,big⟩ := Finset.mem_filter.mp hw
  rw [Finset.mem_range] at hw'
  simp only [support,Finset.card_map] at big
  by_cases hi : w < n+m
  · exact False.elim ((Nat.not_lt_of_ge (orIn_input C w hi)) big)
  obtain ⟨j,rfl⟩ : ∃ j, w = n+m+j := ⟨w-(n+m),by omega⟩
  obtain ⟨x,hx,_,_,_⟩ := Finset.one_lt_card.mp big
  exact ⟨j,by omega,rfl,((orIn_gate C j x).mp hx).2.1⟩

def src (N : ℕ) (C : Circuit) (b : Fin 2) (w : ℕ) := opnd C (w-N) b

theorem lower_local (ao : IsAO2 (n+m) C) (c : V n m) :
    (∀ w < n+m+C.size, w ∉ lower E C c → (edgesAt E c (support C w)).card ≤ 1) ∧
    ∀ w ∈ lower E C c, src (n+m) C 0 w < w ∧ src (n+m) C 1 w < w ∧
      edgesAt E c (support C w) =
        edgesAt E c (support C (src (n+m) C 0 w)) ∪
        edgesAt E c (support C (src (n+m) C 1 w)) := by
  classical
  constructor
  · intro w lt outside
    by_cases fits : Fits E c (support C w)
    · have small : (support (n:=n) (m:=m) C w).card ≤ 1 := by
        by_contra! big
        exact outside (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr lt,fits,big⟩)
      simpa only [edgesAt,ite_eq_left fits] using (star_card c (support C w)).trans small
    · simp only [edgesAt,ite_eq_right fits,Finset.card_empty,Nat.zero_le]
  · intro w hw
    obtain ⟨j,hj,rfl,op⟩ := owned_or hw
    have ins := pair_inputs ao hj
    have lt (s : Fin 2) : opnd C j s < n+m+j := by
      apply ao.2.1 j hj
      rw [ins]
      fin_cases s <;> simp
    have hlen : j < C.gates.length := hj
    have eq : support (n:=n) (m:=m) C (n+m+j) = support C (opnd C j 0) ∪ support C (opnd C j 1) := by
      ext v
      simp only [support_iff,Finset.mem_union,orIn_gate C j,hlen,op,true_and]
      rw [ins]
      simp only [List.mem_pair]
      constructor
      · rintro ⟨w,h | h,_,hv⟩ <;> subst w
        · exact Or.inl hv
        · exact Or.inr hv
      · rintro (h | h)
        · exact ⟨_,Or.inl rfl,lt 0,h⟩
        · exact ⟨_,Or.inr rfl,lt 1,h⟩
    have fits := (Finset.mem_filter.mp hw).2.1
    rw [eq] at fits
    simpa only [src,Nat.add_sub_cancel_left,eq] using
      And.intro (lt 0) (And.intro (lt 1) (edges_split fits))

theorem lower_cost (ao : IsAO2 (n+m) C) (hc : Computes E C) (sq : SquareFree E)
    (A : Finset (V n m)) :
    2 * (frontier (n+m) C .and).card + ∑ c ∈ A, (lower E C c).card ≤ C.size+1 := by
  classical
  let N := n+m
  let X := frontier N C .and
  let Y := frontier N C .or
  let T := A.biUnion (lower E C)
  have unique : (A : Set (V n m)).PairwiseDisjoint (lower E C) := by
    intro c _ d _ ne
    apply Finset.disjoint_left.mpr
    intro w h1 h2
    obtain ⟨_,fit,big⟩ := Finset.mem_filter.mp h1
    exact ne (big_owners sq fit (Finset.mem_filter.mp h2).2.1 big)
  have count := Finset.card_biUnion unique
  let L := T.image (fun w => w-N)
  have Lift {w : ℕ} (hw : w ∈ T) : ∃ j < C.size, w = N+j ∧ (gateAt C j).op = .or ∧ j ∉ Y := by
    obtain ⟨c,_,h⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨j,hj,eq,op⟩ := owned_or h
    refine ⟨j,hj,eq,op,fun hy => ?_⟩
    have zero := frontier_orIn_empty (single_off hc) hy
    have big := (Finset.mem_filter.mp h).2.2
    simp only [eq,support,Finset.card_map,zero,Finset.card_empty] at big
    omega
  have cardL : L.card = T.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb eq
    obtain ⟨j,_,rfl,_,_⟩ := Lift ha
    obtain ⟨k,_,rfl,_,_⟩ := Lift hb
    simpa using eq
  have inL {j : ℕ} (h : j ∈ L) : j < C.size ∧ (gateAt C j).op = .or ∧ j ∉ Y := by
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨j,hj,rfl,op,ex⟩ := Lift hw
    simpa using And.intro hj (And.intro op ex)
  have dxy : Disjoint X Y := by
    refine Finset.disjoint_left.mpr fun j hx hy => ?_
    have eq := (mem_frontier.mp hx).2.1.symm.trans (mem_frontier.mp hy).2.1
    cases eq
  have dz : Disjoint (X ∪ Y) L := by
    apply Finset.disjoint_left.mpr
    intro j h hl
    rcases Finset.mem_union.mp h with hx | hy
    · have eq := (mem_frontier.mp hx).2.1.symm.trans (inL hl).2.1
      cases eq
    · exact (inL hl).2.2 hy
  have sub : X ∪ Y ∪ L ⊆ Finset.range C.size := by
    intro j h
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h <;> exact (mem_frontier.mp h).1
    · exact (inL h).1
  have s := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dz,Finset.card_union_of_disjoint dxy,Finset.card_range,cardL] at s
  have a : X.card ≤ Y.card+1 := frontier_count C ao
  change T.card = _ at count
  change 2*X.card + _ ≤ _
  omega

end Wires

end PEqualNP.Outside.L_meta_5761_aux

open PEqualNP.Outside.L_meta_5761_aux

theorem PEqualNP.Outside.L_meta_5761 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ),   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) →     PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →       (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) →         have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x4;         (∀ x10 ∈ x5, x10 < x1 + x2 ∨ ∃ x12 < x4.size, x10 = x1 + x2 + x12 ∧ (x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x9 x12).inputs, x13 ∈ x5) →           (∀ x11 < x4.size, (x9 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x14 ∈ (x9 x11).inputs, x14 ∈ x5) →             have x12 : ℕ := x1 + x2 + x4.size;             ∃ (x13 : Finset (Fin x1 ⊕ Fin x2)) (x14 : Fin x1 ⊕ Fin x2 → Finset ℕ) (x15 : Fin x1 ⊕ Fin x2 → Finset ℕ) (x16 : Fin x1 ⊕ Fin x2 → ℕ → Finset (Fin x1 × Fin x2)) (x17 : ℕ → ℕ) (x18 : ℕ → ℕ) (x19 : ℕ),               have x20 : Fin x1 ⊕ Fin x2 → Finset (Fin x1 × Fin x2) := fun (x20 : Fin x1 ⊕ Fin x2) => (x14 x20).biUnion (x16 x20);               (∀ x21 ∈ x3, ∃ x23 ∈ x13, x21 ∈ x20 x23) ∧ (∀ x21 ∈ x13, ∀ x23 ∈ x20 x21, x21 = Sum.inl x23.1 ∨ x21 = Sum.inr x23.2) ∧ (∀ x21 ∈ x13, x14 x21 ⊆ Finset.range x12 ∧ x15 x21 ⊆ Finset.range x12 ∧ (∀ x23 < x12, x23 ∉ x15 x21 → (x16 x21 x23).card ≤ (1 : ℕ)) ∧ ∀ x23 ∈ x15 x21, x17 x23 < x23 ∧ x18 x23 < x23 ∧ x16 x21 x23 = x16 x21 (x17 x23) ∪ x16 x21 (x18 x23)) ∧ x13.card ≤ x19 ∧ ∑ x21 ∈ x13, (x14 x21).card ≤ x19 ∧ (2 : ℕ) * x19 + ∑ x21 ∈ x13, (x15 x21).card ≤ x4.size + (1 : ℕ) := by
  intro n m E C U sq ao hc
  dsimp only
  intro pure parents
  classical
  let J := productive n m C
  let P := frontier (n+m) C .and
  have sub : J ⊆ P := Finset.filter_subset _ _
  have budgetJ : J.card ≤ P.card := Finset.card_le_card sub
  choose center root bound fits owns using assign ao hc sq
  let all : Finset {j // j ∈ J} := Finset.univ
  let A := all.image center
  let R := fun c => (all.filter (fun j => center j = c)).image root
  have nall : all.card = J.card := by simp [all]
  have root_mem (j : {j // j ∈ J}) : root j ∈ R (center j) := by
    apply Finset.mem_image.mpr
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩
  refine ⟨A,R,lower E C,(fun c w => edgesAt E c (support C w)),
    src (n+m) C 0,src (n+m) C 1,P.card,?_,?_,?_,?_,?_,lower_cost ao hc sq A⟩
  · rintro ⟨p,l⟩ edge
    obtain ⟨i,hi,alt⟩ := extract ao hc pure parents edge
    let j : {i // i ∈ J} := ⟨i,hi⟩
    refine ⟨center j,Finset.mem_image_of_mem _ (Finset.mem_univ _),
      Finset.mem_biUnion.mpr ⟨root j,root_mem j,?_⟩⟩
    change (p,l) ∈ edgesAt E (center j) (support C (root j))
    simp only [edgesAt,ite_eq_left (fits j),star_mem]
    rcases alt with ⟨hp,hl⟩ | ⟨hl,hp⟩
    · exact owns j _ hp _ hl
    · exact (owns j _ hl _ hp).symm
  · intro c _ e he
    obtain ⟨w,hw,he⟩ := Finset.mem_biUnion.mp he
    change e ∈ edgesAt E c (support C w) at he
    by_cases h : Fits E c (support C w)
    · simp only [edgesAt,ite_eq_left h,star_mem] at he
      exact he.imp And.left And.left
    · simp only [edgesAt,ite_eq_right h,Finset.notMem_empty] at he
  · intro c _
    refine ⟨?_,Finset.filter_subset _ _,lower_local ao c⟩
    intro w hw
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_range.mpr (bound j)
  · exact Finset.card_image_le.trans (nall ▸ budgetJ)
  · calc
      ∑ c ∈ A, (R c).card ≤ ∑ c ∈ A, (all.filter (fun j => center j = c)).card :=
        Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      _ = all.card := (Finset.card_eq_sum_card_image center all).symm
      _ ≤ P.card := nall ▸ budgetJ
