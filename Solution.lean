/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Jiří Chmel

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib

/-!
# Solution: WOWII Conjecture 399b is false (a 12-vertex counterexample)

Conjecture 399b of E. DeLaViña's *Written on the Wall II* (conjectures of Graffiti.pc) says
that every connected graph $G$ on $n > 2$ vertices satisfies
$\gamma_2 \le \mathrm{WP}(\overline{G}) + \lfloor 3/\alpha(G[A_3]) \rfloor$, where $A_3$ is the
set of vertices of degree at least three. `Challenge.lean` states that this is false. This file
proves it with the graph $F_3$ on twelve vertices (graph6 `KCOfFFb?~?[?`): $F_3$ is connected,
$\gamma_2(F_3) = 7$, $\mathrm{WP}(\overline{F_3}) = 6$ and $\alpha(F_3[A_3]) = 4$, so
$\gamma_2(F_3) = 7 > 6 = 6 + \lfloor 3/4 \rfloor$.

The file has four parts.
1. The definitions of `Challenge.lean`, copied verbatim.
2. Namespace `Palomar399b`: a verbatim copy of the part of the authors' Lean development that
   the proof uses (from `LeanWowii/W213/Defs.lean`, `LeanWowii/W213/Audit.lean`,
   `LeanWowii/W399b/Defs.lean` and `LeanWowii/W399b/Counterexample.lean`), with every name
   moved under the prefix `Palomar399b`. Those files do not use Lean's module system, so a
   module cannot import them.
3. Bridge lemmas, for every finite graph: the Challenge's `twoDominationNumber`,
   `welshPowellComplement` and independence number of $G[A_3]$ equal `W213.gamma2`,
   `W399b.wpCompl` and `W399b.alphaA3`; $A_3$ is nonempty iff `0 < W399b.alphaA3 G`; and the
   Challenge's statement without its negation is equivalent to
   `W399b.Conjecture399bStatement`.
4. The values of the Challenge's invariants on $F_3$, and the theorem `conjecture399b`.

The lower bound $\gamma_2(F_3) \ge 7$ is a finite check over all $2^{12}$ vertex subsets, done
by `decide +kernel` in `key_bool`. No `native_decide` is used.
-/

@[expose] public section

/-! ## 1. The definitions of the Challenge, copied verbatim -/

namespace WrittenOnTheWallII.GraphConjecture399b

open SimpleGraph

-- `IsTwoDominating` and `twoDominationNumber` are copied verbatim from the open
-- Formal Conjectures pull request #7320 (WOWII Conjecture 396), at its head commit
-- adb67e65958b.

/-- Every vertex outside the set has at least two neighbors in the set. -/
def IsTwoDominating {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) : Prop :=
  ∀ v ∉ D, 2 ≤ (D.filter fun w => G.Adj v w).card

/-- The minimum order of a 2-dominating set. -/
noncomputable def twoDominationNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n | ∃ D : Finset V, IsTwoDominating G D ∧ D.card = n}

/-- The degrees of `G` in nondecreasing order, $d_1 \le d_2 \le \dots \le d_n$,
as a list indexed from `0`, so that $d_k$ is the entry at index `k - 1`. -/
def sortedDegrees {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v => G.degree v).sort (· ≤ ·)

/-- Welsh-Powell of the complement of `G`, written $\mathrm{WP}(\overline{G})$.
Definition 113 of Written on the Wall II reads: "is the largest k such that the
k + d_k is less than or equal to n, where the degree sequence is order in
nondecreasing order, that is d_1 <= d_2 <= ... d_n." (The catalogue writes the
subscripts in HTML; they are written here with `_`.)

The definition does not say whose degree sequence is meant. Here
$d_1 \le \dots \le d_n$ are read as the degrees of `G`; with this reading the value
is the Welsh-Powell bound for the chromatic number of the complement of `G`.
The index $k$ ranges over $1, \dots, n$. For $n \ge 1$ the value $k = 1$ always
qualifies; the value is `0` only when $n = 0$. -/
def welshPowellComplement {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((Finset.Icc 1 (Fintype.card V)).filter fun k =>
    k + (sortedDegrees G).getD (k - 1) 0 ≤ Fintype.card V).sup id

/-- $A_3$: the set of vertices of degree at least three. -/
def degreeAtLeastThree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => 3 ≤ G.degree v

end WrittenOnTheWallII.GraphConjecture399b

/-! ## 2. The authors' development, copied verbatim under the prefix `Palomar399b` -/

namespace Palomar399b

/-! From `LeanWowii/W213/Defs.lean`, lines 18-163 and 167-189. -/

namespace W213

set_option linter.unusedSectionVars false

open Finset

universe u

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 2-domination -/

section TwoDom

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- "gamma_2 = 2-domination number: the smallest D such that every vertex is in D or adjacent
to 2 vertices of D." A set `D` is 2-dominating if every vertex not in `D` has at least two
neighbours in `D`. -/
def IsTwoDominating (D : Finset V) : Prop :=
  ∀ v, v ∉ D → 2 ≤ (D.filter (G.Adj v)).card

instance (D : Finset V) : Decidable (IsTwoDominating G D) := by
  unfold IsTwoDominating; infer_instance

theorem isTwoDominating_univ : IsTwoDominating G (Finset.univ : Finset V) := by
  intro v hv
  exact absurd (Finset.mem_univ v) hv

theorem exists_twoDominating_card : ∃ k, ∃ D : Finset V, IsTwoDominating G D ∧ D.card = k :=
  ⟨_, _, isTwoDominating_univ G, rfl⟩

/-- The 2-domination number: "the smallest D such that every vertex is in D or adjacent to
2 vertices of D", i.e. the least cardinality of a 2-dominating set. -/
noncomputable def gamma2 : ℕ :=
  @Nat.find _ (Classical.decPred _) (exists_twoDominating_card G)

/-- `gamma2` is attained by some 2-dominating set. -/
theorem gamma2_spec : ∃ D : Finset V, IsTwoDominating G D ∧ D.card = gamma2 G :=
  @Nat.find_spec _ (Classical.decPred _) (exists_twoDominating_card G)

/-- `gamma2` is at most the size of every 2-dominating set. -/
theorem gamma2_le {D : Finset V} (hD : IsTwoDominating G D) : gamma2 G ≤ D.card :=
  @Nat.find_min' _ (Classical.decPred _) (exists_twoDominating_card G) _ ⟨D, hD, rfl⟩

/-- Characterisation: `gamma2 G ≤ k` iff some 2-dominating set has at most `k` vertices. -/
theorem gamma2_le_iff (k : ℕ) :
    gamma2 G ≤ k ↔ ∃ D : Finset V, IsTwoDominating G D ∧ D.card ≤ k := by
  constructor
  · intro h
    obtain ⟨D, hD, hc⟩ := gamma2_spec G
    exact ⟨D, hD, hc ▸ h⟩
  · rintro ⟨D, hD, hc⟩
    exact (gamma2_le G hD).trans hc

/-- Characterisation: `k ≤ gamma2 G` iff every 2-dominating set has at least `k` vertices. -/
theorem le_gamma2_iff (k : ℕ) :
    k ≤ gamma2 G ↔ ∀ D : Finset V, IsTwoDominating G D → k ≤ D.card := by
  constructor
  · intro h D hD
    exact h.trans (gamma2_le G hD)
  · intro h
    obtain ⟨D, hD, hc⟩ := gamma2_spec G
    exact hc ▸ h D hD

theorem gamma2_le_card : gamma2 G ≤ Fintype.card V := by
  simpa using gamma2_le G (isTwoDominating_univ G)

end TwoDom

/-! ## Sorted lists of naturals: counting lemmas -/

section SortedList

theorem sorted_le_getElem {L : List ℕ} (hs : L.Pairwise (· ≤ ·)) {i j : ℕ}
    (hi : i < L.length) (hj : j < L.length) (hij : i ≤ j) : L[i] ≤ L[j] := by
  rcases Nat.eq_or_lt_of_le hij with h | h
  · subst h; exact le_rfl
  · exact List.pairwise_iff_getElem.mp hs i j hi hj h

/-- In a nondecreasing list, the entry at index `k` is `≤ t` iff at least `k+1` entries are
`≤ t`. -/
theorem sorted_getElem_le_iff {L : List ℕ} (hs : L.Pairwise (· ≤ ·)) {k : ℕ}
    (hk : k < L.length) (t : ℕ) :
    L[k] ≤ t ↔ k + 1 ≤ L.countP (fun x => decide (x ≤ t)) := by
  constructor
  · intro h
    have hall : ∀ x ∈ L.take (k + 1), decide (x ≤ t) = true := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
      have hj' : j ≤ k := by omega
      simpa using (sorted_le_getElem hs _ hk hj').trans h
    have h1 := (List.countP_eq_length).mpr hall
    have h2 := (List.take_sublist (k + 1) L).countP_le (p := fun x => decide (x ≤ t))
    rw [h1, List.length_take] at h2
    omega
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have hnone : ∀ x ∈ L.drop k, ¬ decide (x ≤ t) = true := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hx
      have := sorted_le_getElem hs hk (show k + j < L.length by omega) (Nat.le_add_right k j)
      simp only [decide_eq_true_eq, not_le]
      omega
    have h0 := (List.countP_eq_zero).mpr hnone
    have hsplit := List.countP_append (p := fun x => decide (x ≤ t)) (l₁ := L.take k) (l₂ := L.drop k)
    rw [List.take_append_drop, h0] at hsplit
    have h3 := List.countP_le_length (p := fun x => decide (x ≤ t)) (l := L.take k)
    rw [List.length_take] at h3
    omega

/-- In a nondecreasing list of length `N`, `t ≤` the entry at index `k` iff at least `N - k`
entries are `≥ t`. -/
theorem le_sorted_getElem_iff {L : List ℕ} (hs : L.Pairwise (· ≤ ·)) {k : ℕ}
    (hk : k < L.length) (t : ℕ) :
    t ≤ L[k] ↔ L.length - k ≤ L.countP (fun x => decide (t ≤ x)) := by
  constructor
  · intro h
    have hall : ∀ x ∈ L.drop k, decide (t ≤ x) = true := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hx
      simpa using h.trans
        (sorted_le_getElem hs hk (show k + j < L.length by omega) (Nat.le_add_right k j))
    have h1 := (List.countP_eq_length).mpr hall
    have h2 := (List.drop_sublist k L).countP_le (p := fun x => decide (t ≤ x))
    rw [h1, List.length_drop] at h2
    omega
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have hnone : ∀ x ∈ L.take (k + 1), ¬ decide (t ≤ x) = true := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
      have := sorted_le_getElem hs (by omega) hk (show j ≤ k by omega)
      simp only [decide_eq_true_eq, not_le]
      omega
    have h0 := (List.countP_eq_zero).mpr hnone
    have hsplit := List.countP_append (p := fun x => decide (t ≤ x)) (l₁ := L.take (k + 1))
      (l₂ := L.drop (k + 1))
    rw [List.take_append_drop, h0] at hsplit
    have h3 := List.countP_le_length (p := fun x => decide (t ≤ x)) (l := L.drop (k + 1))
    rw [List.length_drop] at h3
    omega

end SortedList

/-! The sorted values (the first part of the section `Median`). -/

section Median

/-- The values `f v` sorted in nondecreasing order: `d_1 ≤ d_2 ≤ ... ≤ d_n`. -/
def sortedValues (f : V → ℕ) : List ℕ :=
  (Finset.univ.val.map f).sort (· ≤ ·)

theorem sortedValues_pairwise (f : V → ℕ) : (sortedValues f).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort _ _

theorem length_sortedValues (f : V → ℕ) : (sortedValues f).length = Fintype.card V := by
  simp [sortedValues, Multiset.length_sort, Finset.card_univ]

theorem countP_sortedValues (f : V → ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (sortedValues f).countP (fun x => decide (p x)) =
      (Finset.univ.filter (fun v => p (f v))).card := by
  have h1 : Multiset.countP p (Finset.univ.val.map f) =
      (sortedValues f).countP (fun x => decide (p x)) := by
    rw [sortedValues]
    conv_lhs => rw [← Multiset.sort_eq (Finset.univ.val.map f) (· ≤ ·)]
    rw [Multiset.coe_countP]
  rw [← h1, Multiset.countP_map]
  rfl

end Median

/-! From `LeanWowii/W213/Audit.lean`, lines 46-51: graphs on `Fin n` from an edge list. -/

namespace Audit

def ofEdges (n : ℕ) (E : List (ℕ × ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => (i.val, j.val) ∈ E)

instance (n : ℕ) (E : List (ℕ × ℕ)) : DecidableRel (ofEdges n E).Adj :=
  fun i j => decidable_of_iff (i ≠ j ∧ ((i.val, j.val) ∈ E ∨ (j.val, i.val) ∈ E))
    (SimpleGraph.fromRel_adj (fun a b : Fin n => (a.val, b.val) ∈ E) i j).symm

end Audit

end W213

/-! From `LeanWowii/W399b/Defs.lean`, lines 22-164. -/

namespace W399b

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

section WP

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The degrees of `G` in nondecreasing order, `d_1 ≤ d_2 ≤ ... ≤ d_n` (as a 0-based list). -/
def sortedDegrees : List ℕ :=
  W213.sortedValues (fun v => G.degree v)

theorem sortedDegrees_pairwise : (sortedDegrees G).Pairwise (· ≤ ·) :=
  W213.sortedValues_pairwise _

theorem length_sortedDegrees : (sortedDegrees G).length = Fintype.card V :=
  W213.length_sortedValues _

/-- Catalogue definition 113: "Welsh-Powell of the complement of G, WP(complement G), is the
largest k such that k + d_k <= n, where the degree sequence is ordered in nondecreasing order
(d_1 <= ... <= d_n)", with the degrees of `G`. Here `k` ranges over `1..n` and
`d_k = (sortedDegrees G)[k-1]`; the value is `0` when no such `k` exists (only when `n = 0`). -/
def wpCompl : ℕ :=
  ((Finset.Icc 1 (Fintype.card V)).filter
      (fun k => k + (sortedDegrees G).getD (k - 1) 0 ≤ Fintype.card V)).sup id

/-- For `1 ≤ k ≤ n`: `k + d_k ≤ n` iff at least `k` vertices have degree `≤ n - k`. -/
theorem add_dk_le_iff {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    k + (sortedDegrees G).getD (k - 1) 0 ≤ Fintype.card V ↔
      k ≤ (univ.filter (fun v => G.degree v + k ≤ Fintype.card V)).card := by
  have hlt : k - 1 < (sortedDegrees G).length := by rw [length_sortedDegrees]; omega
  have hget : (sortedDegrees G).getD (k - 1) 0 = (sortedDegrees G)[k - 1] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  rw [hget]
  have h := W213.sorted_getElem_le_iff (sortedDegrees_pairwise G) hlt (Fintype.card V - k)
  have hc : (sortedDegrees G).countP (fun x => decide (x ≤ Fintype.card V - k)) =
      (univ.filter (fun v => G.degree v ≤ Fintype.card V - k)).card :=
    W213.countP_sortedValues (fun v => G.degree v) (fun x => x ≤ Fintype.card V - k)
  rw [hc] at h
  have hf : (univ.filter (fun v => G.degree v ≤ Fintype.card V - k)) =
      (univ.filter (fun v => G.degree v + k ≤ Fintype.card V)) := by
    apply Finset.filter_congr; intro v _; omega
  rw [hf] at h
  constructor
  · intro h1; have := h.mp (by omega); omega
  · intro h1; have := h.mpr (by omega); omega

/-- Counting characterisation of `wpCompl`: the same maximum over `1..n`, with the condition
`k + d_k ≤ n` replaced by "at least `k` vertices have degree `≤ n - k`". -/
theorem wpCompl_eq_count :
    wpCompl G = ((Finset.Icc 1 (Fintype.card V)).filter
      (fun k => k ≤ (univ.filter (fun v => G.degree v + k ≤ Fintype.card V)).card)).sup id := by
  unfold wpCompl
  congr 1
  apply Finset.filter_congr
  intro k hk
  rw [Finset.mem_Icc] at hk
  exact add_dk_le_iff G hk.1 hk.2

end WP

section Alpha

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `A_3`: the set of vertices of degree at least three. -/
def A3 : Finset V := univ.filter (fun v => 3 ≤ G.degree v)

/-- `S` is an independent set of `G` (no two vertices of `S` are adjacent). -/
def IsIndep (S : Finset V) : Prop := ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

instance (S : Finset V) : Decidable (IsIndep G S) := by unfold IsIndep; infer_instance

theorem isIndep_iff_isIndepSet (S : Finset V) : IsIndep G S ↔ G.IsIndepSet (S : Set V) := by
  constructor
  · intro h u hu v hv _; exact h u hu v hv
  · intro h u hu v hv huv
    exact h hu hv (G.ne_of_adj huv) huv

/-- `alpha(G[A_3])`: the largest size of an independent set of `G` contained in `A_3`, i.e. the
independence number of the subgraph induced by `A_3` (`0` if `A_3` is empty). -/
def alphaA3 : ℕ := ((A3 G).powerset.filter (IsIndep G)).sup Finset.card

theorem card_le_alphaA3 {S : Finset V} (hS : S ⊆ A3 G) (hI : IsIndep G S) :
    S.card ≤ alphaA3 G :=
  Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, hI⟩)

theorem exists_alphaA3 : ∃ S, S ⊆ A3 G ∧ IsIndep G S ∧ S.card = alphaA3 G := by
  have hne : ((A3 G).powerset.filter (IsIndep G)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, by simp [IsIndep]⟩⟩
  obtain ⟨S, hS, he⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  exact ⟨S, hS.1, hS.2, he.symm⟩

/-- Agreement with Mathlib's independence number of the induced subgraph `G[A_3]` (vertex type
the subtype of `A_3`). -/
theorem alphaA3_eq_indepNum :
    alphaA3 G = (G.induce (A3 G : Set V)).indepNum := by
  classical
  apply le_antisymm
  · obtain ⟨S, hS, hI, hc⟩ := exists_alphaA3 G
    rw [← hc]
    let T : Finset (A3 G : Set V) := S.subtype (· ∈ A3 G)
    have hT : T.card = S.card := by
      rw [Finset.card_subtype]; congr 1
      exact Finset.filter_true_of_mem (fun x hx => hS hx)
    rw [← hT]
    apply SimpleGraph.IsIndepSet.card_le_indepNum
    intro a ha b hb _ hab
    have ha' : (a : V) ∈ S := by simpa [T] using ha
    have hb' : (b : V) ∈ S := by simpa [T] using hb
    exact hI a ha' b hb' hab
  · obtain ⟨T, hT⟩ := (G.induce (A3 G : Set V)).exists_isNIndepSet_indepNum
    rw [← hT.card_eq]
    have hle := card_le_alphaA3 G (S := T.map (Function.Embedding.subtype _))
      (by intro x hx; obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hx; exact y.property)
      (by
        intro u hu v hv huv
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
        have hab : a ≠ b := by rintro rfl; exact G.loopless.irrefl _ huv
        exact hT.isIndepSet ha hb hab huv)
    simpa using hle

end Alpha

/-- Conjecture 399b (Graffiti.pc, Written on the Wall II): "If G is a connected graph on
n > 2 vertices, then gamma_2 <= WP(complement of G) + FLOOR[3/alpha(G[A_3])]". The extra
hypothesis `0 < alphaA3 G` (i.e. `A_3` nonempty) excludes the graphs where the right side is
undefined; it only weakens the statement, so refuting it refutes the catalogue statement.
`3 / alphaA3 G` is natural-number division, i.e. the floor. -/
def Conjecture399bStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → 2 < Fintype.card V → 0 < alphaA3 G →
      W213.gamma2 G ≤ wpCompl G + 3 / alphaA3 G

end W399b

/-! From `LeanWowii/W399b/Counterexample.lean`, lines 23-195. -/

namespace W399b

set_option linter.unusedSectionVars false

open Finset

/-! ## The graph -/

/-- The 24 edges of F_3: `x_i l_i`; the triangle on `K = {6,7,8}`; `X × K`; `w × K`; `Y × X`. -/
def edgesF3 : List (ℕ × ℕ) :=
  [(0,3),(1,4),(2,5),                               -- x_i l_i
   (6,7),(6,8),(7,8),                               -- K is a triangle
   (0,6),(0,7),(0,8),(1,6),(1,7),(1,8),(2,6),(2,7),(2,8),  -- X joined to K
   (9,6),(9,7),(9,8),                               -- w joined to K
   (10,0),(10,1),(10,2),(11,0),(11,1),(11,2)]       -- Y joined to X

/-- The graph F_3 (Definition 2 of the paper with q = 3), on `Fin 12`. -/
abbrev F3 : SimpleGraph (Fin 12) := W213.Audit.ofEdges 12 edgesF3

example : edgesF3.length = 24 := rfl

/-- Explicit neighbour lists. -/
def nbL : Fin 12 → List (Fin 12)
  | 0 => [3,6,7,8,10,11] | 1 => [4,6,7,8,10,11] | 2 => [5,6,7,8,10,11]
  | 3 => [0] | 4 => [1] | 5 => [2]
  | 6 => [0,1,2,7,8,9] | 7 => [0,1,2,6,8,9] | 8 => [0,1,2,6,7,9]
  | 9 => [6,7,8] | 10 => [0,1,2] | 11 => [0,1,2]

set_option maxRecDepth 10000 in
theorem adj_iff_mem_nbL : ∀ v u : Fin 12, F3.Adj v u ↔ u ∈ nbL v := by decide +kernel

theorem nbL_nodup : ∀ v : Fin 12, (nbL v).Nodup := by decide +kernel

set_option maxRecDepth 10000 in
/-- Degrees: leaves 1, `y_a` 3, `w` 3, `x_i` and `k_j` 6. -/
theorem degree_F3 : ∀ v : Fin 12, F3.degree v = (nbL v).length := by decide +kernel

/-! ## Connectivity -/

theorem reach_from_6 (v : Fin 12) : F3.Reachable 6 v := by
  have a : ∀ a b : Fin 12, F3.Adj a b → F3.Reachable a b := fun _ _ h => h.reachable
  fin_cases v
  · exact a 6 0 (by decide)
  · exact a 6 1 (by decide)
  · exact a 6 2 (by decide)
  · exact (a 6 0 (by decide)).trans (a 0 3 (by decide))
  · exact (a 6 1 (by decide)).trans (a 1 4 (by decide))
  · exact (a 6 2 (by decide)).trans (a 2 5 (by decide))
  · exact SimpleGraph.Reachable.refl _
  · exact a 6 7 (by decide)
  · exact a 6 8 (by decide)
  · exact a 6 9 (by decide)
  · exact (a 6 0 (by decide)).trans (a 0 10 (by decide))
  · exact (a 6 0 (by decide)).trans (a 0 11 (by decide))

theorem F3_connected : F3.Connected :=
  ⟨fun u v => (reach_from_6 u).symm.trans (reach_from_6 v)⟩

/-! ## WP(complement of F_3) = 6 -/

set_option maxRecDepth 100000 in
theorem wpCompl_F3 : wpCompl F3 = 6 := by
  rw [wpCompl_eq_count]; simp only [Fintype.card_fin]; decide +kernel

/-- The sorted degree sequence itself, for the record (the list is computed with
`Multiset.sort`, so it is checked through the counting lemma rather than by evaluation). -/
theorem wpCompl_F3_witness :
    6 + (sortedDegrees F3).getD 5 0 ≤ 12 ∧ ∀ k, 7 ≤ k → k ≤ 12 →
      ¬ k + (sortedDegrees F3).getD (k - 1) 0 ≤ 12 := by
  have h := fun k (h1 : 1 ≤ k) (h2 : k ≤ 12) =>
    add_dk_le_iff F3 (k := k) h1 (by simpa using h2)
  simp only [Fintype.card_fin] at h
  refine ⟨(h 6 (by norm_num) (by norm_num)).mpr (by decide +kernel), ?_⟩
  intro k hk1 hk2
  rw [h k (by omega) hk2]
  interval_cases k <;> decide +kernel

/-! ## A_3 and alpha(F_3[A_3]) = 4 -/

set_option maxRecDepth 10000 in
theorem A3_F3 : A3 F3 = {0, 1, 2, 6, 7, 8, 9, 10, 11} := by decide +kernel

set_option maxRecDepth 100000 in
theorem alphaA3_F3 : alphaA3 F3 = 4 := by
  unfold alphaA3; rw [A3_F3]; decide +kernel

/-- The independent set `X ∪ {w}` of the paper. -/
example : {0, 1, 2, 9} ⊆ A3 F3 ∧ IsIndep F3 {0, 1, 2, 9} := by
  rw [A3_F3]; decide +kernel

/-! ## gamma_2(F_3) = 7 -/

/-- Counting the members of `D` along a duplicate-free list. -/
theorem card_filter_toFinset {α : Type*} [DecidableEq α] (D : Finset α) :
    ∀ L : List α, L.Nodup →
      (L.toFinset.filter (· ∈ D)).card = L.countP (fun u => decide (u ∈ D))
  | [], _ => by simp
  | a :: L, h => by
    rw [List.nodup_cons] at h
    have ih := card_filter_toFinset D L h.2
    rw [List.toFinset_cons, Finset.filter_insert, List.countP_cons]
    by_cases ha : a ∈ D
    · simp only [ha, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp [h.1]), ih]; simp
    · simp only [ha, ↓reduceIte]
      rw [ih]; simp

theorem card_filter_adj (D : Finset (Fin 12)) (v : Fin 12) :
    (D.filter (F3.Adj v)).card = (nbL v).countP (fun u => decide (u ∈ D)) := by
  rw [← card_filter_toFinset D (nbL v) (nbL_nodup v)]
  congr 1
  ext u
  simp only [Finset.mem_filter, List.mem_toFinset, adj_iff_mem_nbL]
  exact and_comm

theorem card_eq_countP (D : Finset (Fin 12)) :
    D.card = (List.finRange 12).countP (fun u => decide (u ∈ D)) := by
  rw [← card_filter_toFinset D _ (List.nodup_finRange 12)]
  congr 1
  ext u
  simp

/-- 2-domination in F_3, read along the neighbour lists. -/
theorem twoDom_iff (D : Finset (Fin 12)) :
    W213.IsTwoDominating F3 D ↔
      ∀ v : Fin 12, v ∉ D → 2 ≤ (nbL v).countP (fun u => decide (u ∈ D)) := by
  unfold W213.IsTwoDominating
  simp only [card_filter_adj]

set_option maxRecDepth 100000 in
/-- The finite check: every Boolean assignment to the 12 vertices that satisfies the
2-domination condition along the neighbour lists has at least 7 `true` entries. -/
theorem key_bool : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool,
    (∀ v : Fin 12, ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] v = false →
      2 ≤ (nbL v).countP ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]) →
    7 ≤ (List.finRange 12).countP ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] := by
  decide +kernel

theorem seven_le_card (D : Finset (Fin 12)) (hD : W213.IsTwoDominating F3 D) :
    7 ≤ D.card := by
  set f : Fin 12 → Bool := fun u => decide (u ∈ D) with hf
  have hvec : ![f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11] = f := by
    funext i; fin_cases i <;> rfl
  have hk := key_bool (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9) (f 10) (f 11)
  rw [hvec] at hk
  rw [card_eq_countP]
  apply hk
  intro v hv
  have hv' : v ∉ D := by simpa [hf] using hv
  exact (twoDom_iff D).mp hD v hv'

/-- The 2-dominating set `D_0 = {l_1,l_2,l_3,x_1,x_2,x_3,w}` of the paper. -/
theorem twoDom_D0 : W213.IsTwoDominating F3 {0, 1, 2, 3, 4, 5, 9} := by
  rw [twoDom_iff]; decide +kernel

theorem gamma2_F3 : W213.gamma2 F3 = 7 := by
  apply le_antisymm
  · exact (W213.gamma2_le F3 twoDom_D0).trans (by decide)
  · exact (W213.le_gamma2_iff F3 7).mpr seven_le_card

/-! ## The main theorem -/

/-- F_3 violates the inequality: `gamma_2 = 7 > 6 = WP(complement) + ⌊3/4⌋`. -/
theorem F3_violates : wpCompl F3 + 3 / alphaA3 F3 < W213.gamma2 F3 := by
  rw [wpCompl_F3, alphaA3_F3, gamma2_F3]
  norm_num

/-- Conjecture 399b of Written on the Wall II is false. -/
theorem not_conjecture399b : ¬ Conjecture399bStatement := by
  intro h
  have hle := h (Fin 12) F3 F3_connected (by simp) (by rw [alphaA3_F3]; norm_num)
  exact absurd hle (not_le.mpr F3_violates)

end W399b

end Palomar399b

/-! ## 3. Bridge lemmas, for every finite graph -/

namespace WrittenOnTheWallII.GraphConjecture399b

open SimpleGraph

section Bridge

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The Challenge's 2-domination is `W213.IsTwoDominating`: the two bodies differ only by an
η-expansion and by the binder notation `∀ v ∉ D`. -/
theorem isTwoDominating_iff (D : Finset V) :
    IsTwoDominating G D ↔ Palomar399b.W213.IsTwoDominating G D :=
  Iff.rfl

/-- Bridge 1: the Challenge's `twoDominationNumber` (an infimum) is `W213.gamma2`
(a `Nat.find`). -/
theorem twoDominationNumber_eq_gamma2 :
    twoDominationNumber G = Palomar399b.W213.gamma2 G := by
  have hne : {n | ∃ D : Finset V, IsTwoDominating G D ∧ D.card = n}.Nonempty :=
    ⟨_, Finset.univ, fun v hv => absurd (Finset.mem_univ v) hv, rfl⟩
  apply le_antisymm
  · obtain ⟨D, hD, hc⟩ := Palomar399b.W213.gamma2_spec G
    exact Nat.sInf_le ⟨D, hD, hc⟩
  · obtain ⟨D, hD, hc⟩ := Nat.sInf_mem hne
    exact (Palomar399b.W213.gamma2_le G hD).trans_eq hc

/-- Bridge 2: the Challenge's `sortedDegrees` is `W399b.sortedDegrees`. -/
theorem sortedDegrees_eq : sortedDegrees G = Palomar399b.W399b.sortedDegrees G :=
  rfl

/-- Bridge 2: the Challenge's `welshPowellComplement` is `W399b.wpCompl`. -/
theorem welshPowellComplement_eq_wpCompl :
    welshPowellComplement G = Palomar399b.W399b.wpCompl G :=
  rfl

/-- Bridge 3: the Challenge's $A_3$ is `W399b.A3`. -/
theorem degreeAtLeastThree_eq_A3 : degreeAtLeastThree G = Palomar399b.W399b.A3 G :=
  rfl

/-- Bridge 3: the Challenge's $\alpha(G[A_3])$, Mathlib's independence number of the induced
subgraph, is `W399b.alphaA3`. -/
theorem indepNum_eq_alphaA3 :
    (G.induce (degreeAtLeastThree G : Set V)).indepNum = Palomar399b.W399b.alphaA3 G :=
  (Palomar399b.W399b.alphaA3_eq_indepNum G).symm

/-- Bridge 4: $A_3$ is nonempty iff $\alpha(G[A_3]) > 0$, the hypothesis used by
`W399b.Conjecture399bStatement`. -/
theorem degreeAtLeastThree_nonempty_iff :
    (degreeAtLeastThree G).Nonempty ↔ 0 < Palomar399b.W399b.alphaA3 G := by
  constructor
  · rintro ⟨v, hv⟩
    have h := Palomar399b.W399b.card_le_alphaA3 G (S := {v})
      (Finset.singleton_subset_iff.mpr hv)
      (by
        intro a ha b hb hab
        rw [Finset.mem_singleton] at ha hb
        subst ha hb
        exact G.ne_of_adj hab rfl)
    rw [Finset.card_singleton] at h
    omega
  · intro h
    obtain ⟨S, hS, -, hc⟩ := Palomar399b.W399b.exists_alphaA3 G
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    exact ⟨v, hS hv⟩

end Bridge

/-- Bridge 5: the Challenge's statement, without its negation, is equivalent to
`W399b.Conjecture399bStatement`. -/
theorem statement_iff_conjecture399bStatement :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 2 < Fintype.card V → (degreeAtLeastThree G).Nonempty →
        twoDominationNumber G ≤
          welshPowellComplement G +
            3 / (G.induce (degreeAtLeastThree G : Set V)).indepNum) ↔
      Palomar399b.W399b.Conjecture399bStatement := by
  unfold Palomar399b.W399b.Conjecture399bStatement
  constructor
  · intro h V _ _ G _ hG hn ha
    have hle := h V G hG hn ((degreeAtLeastThree_nonempty_iff G).mpr ha)
    rwa [twoDominationNumber_eq_gamma2, welshPowellComplement_eq_wpCompl,
      indepNum_eq_alphaA3] at hle
  · intro h V _ _ G _ hG hn ha
    rw [twoDominationNumber_eq_gamma2, welshPowellComplement_eq_wpCompl, indepNum_eq_alphaA3]
    exact h V G hG hn ((degreeAtLeastThree_nonempty_iff G).mp ha)

/-! ## 4. The values on $F_3$, and the theorem -/

/-- $\gamma_2(F_3) = 7$. -/
theorem twoDominationNumber_F3 : twoDominationNumber Palomar399b.W399b.F3 = 7 := by
  rw [twoDominationNumber_eq_gamma2]
  exact Palomar399b.W399b.gamma2_F3

/-- $\mathrm{WP}(\overline{F_3}) = 6$. -/
theorem welshPowellComplement_F3 : welshPowellComplement Palomar399b.W399b.F3 = 6 := by
  rw [welshPowellComplement_eq_wpCompl]
  exact Palomar399b.W399b.wpCompl_F3

/-- $A_3$ of $F_3$: every vertex except the three leaves $3, 4, 5$. -/
theorem degreeAtLeastThree_F3 :
    degreeAtLeastThree Palomar399b.W399b.F3 = {0, 1, 2, 6, 7, 8, 9, 10, 11} :=
  Palomar399b.W399b.A3_F3

/-- $\alpha(F_3[A_3]) = 4$. -/
theorem indepNum_F3 :
    (Palomar399b.W399b.F3.induce
      (degreeAtLeastThree Palomar399b.W399b.F3 : Set (Fin 12))).indepNum = 4 := by
  rw [indepNum_eq_alphaA3]
  exact Palomar399b.W399b.alphaA3_F3

/-- $F_3$ has twelve vertices. -/
theorem card_F3 : Fintype.card (Fin 12) = 12 :=
  Fintype.card_fin 12

set_option maxRecDepth 100000 in
/-- Not needed for `conjecture399b`. Definition 113 does not say whose degree sequence is meant;
the Challenge uses the degrees of $G$. With the degrees of the complement instead, the same
formula is `welshPowellComplement` of $\overline{F_3}$, and it is also $6$, so $F_3$ is a
counterexample under both readings. -/
theorem welshPowellComplement_compl_F3 :
    welshPowellComplement Palomar399b.W399b.F3ᶜ = 6 := by
  rw [welshPowellComplement_eq_wpCompl, Palomar399b.W399b.wpCompl_eq_count]
  simp only [Fintype.card_fin]
  decide +kernel

/--
WOWII Conjecture 399b states: "If $G$ is a connected graph on $n > 2$ vertices,
then $\gamma_2 \le \mathrm{WP}(\overline{G}) + \lfloor 3/\alpha(G[A_3]) \rfloor$,
where $A_3$ is the set vertices of degree at least three."

Definition 90 of Written on the Wall II reads: "A subset of the vertices, D_2, of
the graph is called a 2-dominating set of the graph if for every vertex v of the
graph, either in v is D_2 or v is adjacent to 2 vertices of D_2. The 2-domination
number of a graph is the size of a smallest 2-dominating set of the graph." (The
catalogue writes the subscripts and italics in HTML; subscripts are written here
with `_`.) "Adjacent to 2 vertices" is read as "adjacent to at least two
vertices", the standard meaning; this is `IsTwoDominating`.

Here $\gamma_2$ is `twoDominationNumber G`, $\mathrm{WP}(\overline{G})$ is
`welshPowellComplement G`, $A_3$ is `degreeAtLeastThree G`, and
$\alpha(G[A_3])$ is the independence number of the induced subgraph; `/` on `ℕ`
is floor division. When $A_3$ is empty, $\alpha(G[A_3]) = 0$ and the source's
right side $3/0$ is undefined, so the statement assumes that $A_3$ is nonempty.
This hypothesis only weakens the conjecture, so its negation, stated here, is
the stronger claim.
-/
theorem conjecture399b : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 2 < Fintype.card V → (degreeAtLeastThree G).Nonempty →
        twoDominationNumber G ≤
          welshPowellComplement G +
            3 / (G.induce (degreeAtLeastThree G : Set V)).indepNum := by
  intro h
  have hle := h (Fin 12) Palomar399b.W399b.F3 Palomar399b.W399b.F3_connected (by simp)
    ⟨0, by rw [degreeAtLeastThree_F3]; simp⟩
  rw [twoDominationNumber_F3, welshPowellComplement_F3, indepNum_F3] at hle
  norm_num at hle

/-- The same theorem, obtained from the authors' `W399b.not_conjecture399b` through the
bridge lemmas. -/
theorem conjecture399b_via_bridge : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 2 < Fintype.card V → (degreeAtLeastThree G).Nonempty →
        twoDominationNumber G ≤
          welshPowellComplement G +
            3 / (G.induce (degreeAtLeastThree G : Set V)).indepNum := fun h =>
  Palomar399b.W399b.not_conjecture399b (statement_iff_conjecture399bStatement.mp h)

end WrittenOnTheWallII.GraphConjecture399b
