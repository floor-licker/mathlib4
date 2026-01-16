module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Pairwise

/-!
# Menger-type lemmas (work in progress)

This file sets up basic definitions for families of edge-disjoint paths and internally
vertex-disjoint paths.

It proves the easy directions towards Menger-type results:

* `k` edge-disjoint `u`-`v` paths imply `k`-edge-reachability.
* `k` internally vertex-disjoint `u`-`v` paths imply reachability persists after deleting
  fewer than `k` vertices.

The converse directions (extracting disjoint paths from these reachability hypotheses, under
finiteness hypotheses) are currently not in mathlib.
-/

@[expose] public section

open Function

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (u v : V) (k : ℕ)

/-- `G.EdgeDisjointPaths u v k` means that there exist `k` paths from `u` to `v` whose edge sets are
pairwise disjoint. -/
def EdgeDisjointPaths : Prop :=
  ∃ paths : Fin k → G.Path u v, Pairwise (Disjoint on fun i : Fin k => (paths i : G.Walk u v).edgeSet)

variable {G u v k}

theorem EdgeDisjointPaths.isEdgeReachable (h : G.EdgeDisjointPaths u v k) : G.IsEdgeReachable k u v := by
  classical
  rcases h with ⟨paths, hpaths⟩
  cases k with
  | zero =>
    simpa using (SimpleGraph.IsEdgeReachable.zero (G := G) (u := u) (v := v))
  | succ k =>
    intro s hs
    have hsFinite : s.Finite := Set.finite_of_encard_le_coe (k := k.succ) (le_of_lt hs)
    have hexists : ∃ i : Fin k.succ, Disjoint s ((paths i : G.Walk u v).edgeSet) := by
      by_contra hno
      have hall : ∀ i : Fin k.succ, ¬ Disjoint s ((paths i : G.Walk u v).edgeSet) := by
        intro i hi
        exact hno ⟨i, hi⟩
      classical
      choose e he_mem_s he_mem_path using fun i : Fin k.succ =>
        Set.not_disjoint_iff.mp (hall i)
      let f : Fin k.succ → s := fun i => ⟨e i, he_mem_s i⟩
      have hf : Injective f := by
        intro i j hij
        have hval : e i = e j := congrArg Subtype.val hij
        by_contra hne
        have hdisj := hpaths hne
        exact (Set.disjoint_left.mp hdisj) (he_mem_path i) (by simpa [hval] using he_mem_path j)
      letI : Fintype s := hsFinite.fintype
      have hk_le : k.succ ≤ s.ncard := by
        have hk_le' : k.succ ≤ Fintype.card s := by
          simpa using (Fintype.card_le_of_injective f hf)
        have hcard : Fintype.card s = s.ncard := by
          simpa [Nat.card_coe_set_eq] using (Nat.card_eq_fintype_card (α := s)).symm
        simpa [hcard] using hk_le'
      have hk_le' : (k.succ : ℕ∞) ≤ s.encard := by
        have hk_le'' : (k.succ : ℕ∞) ≤ s.ncard := Nat.cast_le.mpr hk_le
        simpa [hsFinite.cast_ncard_eq] using hk_le''
      exact (not_lt_of_ge hk_le') hs
    rcases hexists with ⟨i, hi⟩
    refine ⟨(paths i : G.Walk u v).toDeleteEdges s ?_⟩
    intro e he
    have he' : e ∈ (paths i : G.Walk u v).edgeSet := by simpa using (Walk.mem_edgeSet.2 he)
    intro hes
    exact (Set.disjoint_left.mp hi) hes he'

namespace Path

variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- The set of *internal* vertices of a path, i.e. vertices in the support other than the
endpoints. -/
def internalVerts (p : G.Path u v) : Set V :=
  {x | x ∈ (p : G.Walk u v).support ∧ x ≠ u ∧ x ≠ v}

@[simp]
lemma mem_internalVerts_iff {p : G.Path u v} {x : V} :
    x ∈ p.internalVerts ↔ x ∈ (p : G.Walk u v).support ∧ x ≠ u ∧ x ≠ v :=
  Iff.rfl

end Path

variable {V : Type*} (G : SimpleGraph V) (k : ℕ) (u v : V)

/-- `G.InternallyVertexDisjointPaths u v k` means that there exist `k` paths from `u` to `v` whose
internal vertex sets are pairwise disjoint. -/
def InternallyVertexDisjointPaths : Prop :=
  ∃ paths : Fin k → G.Path u v,
    Pairwise (Disjoint on fun i : Fin k => (paths i).internalVerts (u := u) (v := v))

variable (G k u v) in
/-- Two vertices remain reachable after deleting strictly fewer than `k` vertices
(not including the endpoints). -/
def IsVertexReachable : Prop :=
  ∀ ⦃s : Set V⦄, s.encard < k → u ∉ s → v ∉ s →
    (G.induce sᶜ).Reachable ⟨u, by simpa⟩ ⟨v, by simpa⟩

variable {G k u v}

@[simp]
theorem IsVertexReachable.zero : G.IsVertexReachable 0 u v := by
  simp [IsVertexReachable]

section VertexSeparator

variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- A *vertex separator* for `u` and `v` is a set of vertices (not containing `u` or `v`) whose
removal disconnects `u` from `v`. This is the notion of a vertex cut used in the vertex version of
Menger's theorem. -/
structure IsVertexSeparator (G : SimpleGraph V) (u v : V) (s : Set V) : Prop where
  not_mem_left : u ∉ s
  not_mem_right : v ∉ s
  not_reachable :
    ¬ (G.induce sᶜ).Reachable
        ⟨u, by simpa using not_mem_left⟩
        ⟨v, by simpa using not_mem_right⟩

/-- The (extended) size of a minimum vertex separator between `u` and `v`. -/
noncomputable def vertexSeparatorNum (G : SimpleGraph V) (u v : V) : ℕ∞ :=
  ⨅ (s : Set V) (_ : IsVertexSeparator G u v s), s.encard

theorem IsVertexReachable.le_vertexSeparatorNum (h : G.IsVertexReachable k u v) :
    (k : ℕ∞) ≤ vertexSeparatorNum G u v := by
  classical
  refine le_iInf fun s => le_iInf fun hs => ?_
  by_contra hk
  have hk' : s.encard < k := lt_of_not_ge hk
  exact hs.not_reachable (h hk' hs.not_mem_left hs.not_mem_right)

end VertexSeparator

theorem InternallyVertexDisjointPaths.isVertexReachable (h : G.InternallyVertexDisjointPaths u v k) :
    G.IsVertexReachable k u v := by
  classical
  rcases h with ⟨paths, hpaths⟩
  cases k with
  | zero =>
    simpa using (IsVertexReachable.zero (G := G) (u := u) (v := v))
  | succ k =>
    intro s hs hu hv
    have hsFinite : s.Finite := Set.finite_of_encard_le_coe (k := k.succ) (le_of_lt hs)
    have hexists : ∃ i : Fin k.succ,
        Disjoint s ((paths i).internalVerts (u := u) (v := v)) := by
      by_contra hno
      have hall : ∀ i : Fin k.succ, ¬ Disjoint s ((paths i).internalVerts (u := u) (v := v)) := by
        intro i hi
        exact hno ⟨i, hi⟩
      choose x hx_mem_s hx_mem_internal using fun i : Fin k.succ =>
        Set.not_disjoint_iff.mp (hall i)
      let f : Fin k.succ → s := fun i => ⟨x i, hx_mem_s i⟩
      have hf : Injective f := by
        intro i j hij
        have hval : x i = x j := congrArg Subtype.val hij
        by_contra hne
        have hdisj := hpaths hne
        have hxj : x i ∈ (paths j).internalVerts (u := u) (v := v) := by
          simpa [hval] using hx_mem_internal j
        exact (Set.disjoint_left.mp hdisj) (hx_mem_internal i) hxj
      letI : Fintype s := hsFinite.fintype
      have hk_le : k.succ ≤ s.ncard := by
        have hk_le' : k.succ ≤ Fintype.card s := by
          simpa using (Fintype.card_le_of_injective f hf)
        have hcard : Fintype.card s = s.ncard := by
          simpa [Nat.card_coe_set_eq] using (Nat.card_eq_fintype_card (α := s)).symm
        simpa [hcard] using hk_le'
      have hk_le' : (k.succ : ℕ∞) ≤ s.encard := by
        have hk_le'' : (k.succ : ℕ∞) ≤ s.ncard := Nat.cast_le.mpr hk_le
        simpa [hsFinite.cast_ncard_eq] using hk_le''
      exact (not_lt_of_ge hk_le') hs
    rcases hexists with ⟨i, hi⟩
    let p : G.Walk u v := (paths i : G.Walk u v)
    have hw : ∀ x ∈ p.support, x ∈ (sᶜ : Set V) := by
      intro x hx
      have hx' : x ∉ s := by
        by_cases hxu : x = u
        · simpa [hxu] using hu
        by_cases hxv : x = v
        · simpa [hxv] using hv
        have hxint : x ∈ (paths i).internalVerts (u := u) (v := v) := ⟨hx, hxu, hxv⟩
        exact (Set.disjoint_right.mp hi) hxint
      simpa using hx'
    refine ⟨(p.induce (s := (sᶜ : Set V)) hw).copy ?_ ?_⟩
    · ext
      rfl
    · ext
      rfl

theorem InternallyVertexDisjointPaths.le_vertexSeparatorNum
    (h : G.InternallyVertexDisjointPaths u v k) : (k : ℕ∞) ≤ vertexSeparatorNum G u v :=
  (h.isVertexReachable).le_vertexSeparatorNum

end SimpleGraph
