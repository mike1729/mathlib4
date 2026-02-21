/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Defs.Sequences
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Countably compact sets

A set is **countably compact** if every sequence in the set has a cluster point in the set.
This is a weaker notion than compactness, but stronger than sequential compactness in general
topological spaces. In metric spaces, countable compactness is equivalent to compactness,
but in general topological spaces it is strictly weaker.

This file defines countably compact sets and proves some basic properties, including the fact that
compact sets and sequentially compact sets are countably compact.

-/

@[expose] public section

noncomputable section

open Set Filter Topology

variable {E : Type*} [TopologicalSpace E]

/-- A set is countably compact if every sequence in the set has a cluster point in the set. -/
def IsCountablyCompact (A : Set E) : Prop :=
  ∀ x : ℕ → E, (∀ n, x n ∈ A) → ∃ a ∈ A, MapClusterPt a atTop x

/-- A topological space is countably compact if every sequence has a cluster point. -/
class CountablyCompactSpace (E : Type*) [TopologicalSpace E] : Prop where
  isCountablyCompact_univ : IsCountablyCompact (Set.univ : Set E)

theorem isCountablyCompact_empty : IsCountablyCompact (∅ : Set E) :=
  fun _ hx => (hx 0).elim

theorem isCountablyCompact_singleton {x : E} : IsCountablyCompact ({x} : Set E) :=
  fun _ hu => ⟨x, mem_singleton x,
    (tendsto_const_nhds.congr fun n => (mem_singleton_iff.mp (hu n)).symm).mapClusterPt⟩

theorem IsCountablyCompact.mono {A B : Set E} (hA : IsCountablyCompact A) (hB : IsClosed B)
    (hBA : B ⊆ A) : IsCountablyCompact B := fun x hx =>
  let ⟨a, _, hac⟩ := hA x (fun n => hBA (hx n))
  ⟨a, hB.mem_of_mapClusterPt hac (Eventually.of_forall hx), hac⟩

theorem isCountablyCompact_iff_clusterPt_countably_generated_filter {A : Set E} :
    IsCountablyCompact A ↔
      ∀ (f : Filter E) [NeBot f] [Filter.IsCountablyGenerated f],
        f ≤ 𝓟 A → ∃ a ∈ A, ClusterPt a f := by
  constructor
  · intro hA f _ _ hle
    obtain ⟨s, hs⟩ := f.exists_antitone_basis
    have hmem : ∀ n, (s n ∩ A).Nonempty := by
      intro n
      exact Filter.nonempty_of_mem (Filter.inter_mem (hs.mem n) (le_principal_iff.mp hle))
    choose x hx using hmem
    obtain ⟨a, ha, hac⟩ := hA x (fun n => (hx n).2)
    exact ⟨a, ha, ClusterPt.mono hac (hs.tendsto (fun n => (hx n).1))⟩
  · intro h x hx
    have : map x atTop ≤ 𝓟 A := le_principal_iff.mpr (mem_map.mpr (Eventually.of_forall hx))
    obtain ⟨a, ha, hac⟩ := h (map x atTop) this
    exact ⟨a, ha, hac⟩

/-- A point `a` is a cluster point of the sequence `x` if and only if `a` belongs to the closure
of every tail `x '' {n | i ≤ n}`. -/
theorem mapClusterPt_atTop_iff_forall_mem_closure {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {x : ι → E} {a : E} :
    MapClusterPt a atTop x ↔ ∀ i, a ∈ closure (x '' Ici i) :=
  show ClusterPt a (map x atTop) ↔ _ by
    simp only [(atTop_basis.map x).clusterPt_iff_forall_mem_closure, true_implies]

theorem isCountablyCompact_iff_countable_open_cover {A : Set E} :
    IsCountablyCompact A ↔
      ∀ (U : ℕ → Set E), (∀ i, IsOpen (U i)) → A ⊆ ⋃ i, U i →
        ∃ t : Finset ℕ, A ⊆ ⋃ i ∈ t, U i := by
  constructor
  · intro hA U hUo hAU
    by_contra h
    push_neg at h
    choose x hxA hxU using fun n => Set.not_subset.mp (h (Finset.range (n + 1)))
    obtain ⟨a, haA, hac⟩ := hA x hxA
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hAU haA)
    have : ∀ᶠ n in atTop, x n ∉ U k :=
      Eventually.mono (Ici_mem_atTop k) fun n hn hxn =>
        hxU n (mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)) hxn)
    exact hac.frequently ((hUo k).mem_nhds hk) this
  · intro h x hx
    by_contra hac
    push_neg at hac
    let V : ℕ → Set E := fun n => (closure (x '' Ici n))ᶜ
    have hVmono : Monotone V := fun m n hmn =>
      compl_subset_compl.mpr (closure_mono (image_mono (Ici_subset_Ici.mpr hmn)))
    have hAV : A ⊆ ⋃ n, V n := by
      intro a haA
      simp only [mapClusterPt_atTop_iff_forall_mem_closure, not_forall] at hac
      obtain ⟨n, hna⟩ := hac a haA
      exact mem_iUnion.mpr ⟨n, mem_compl hna⟩
    obtain ⟨t, ht⟩ := h V (fun n => isClosed_closure.isOpen_compl) hAV
    have : ∀ᶠ n in atTop, ∀ j ∈ t, x n ∉ V j :=
      (eventually_all_finset t).mpr fun j _ =>
        Eventually.mono (Ici_mem_atTop j) fun n hn hxn =>
          hVmono hn hxn (subset_closure ⟨n, mem_Ici.mpr le_rfl, rfl⟩)
    obtain ⟨n, hn⟩ := this.exists
    obtain ⟨j, hjt, hjV⟩ := mem_iUnion₂.mp (ht (hx n))
    exact hn j hjt hjV

theorem IsCompact.IsCountablyCompact {A : Set E} (hA : IsCompact A) : IsCountablyCompact A :=
  fun _ h_mem => hA (le_principal_iff.2 (mem_map.2 (Eventually.of_forall h_mem)))

theorem IsSeqCompact.IsCountablyCompact {A : Set E} (hA : IsSeqCompact A) :
    IsCountablyCompact A := by
  intro x h_mem
  obtain ⟨a, ha_mem, φ, hφ_mono, hφ_tendsto⟩ := hA h_mem
  exact ⟨a, ha_mem, (hφ_tendsto.mapClusterPt).of_comp hφ_mono.tendsto_atTop⟩


-- isCountablyCompact_iff_infinite_subset_has_limit_point
-- [SecondCountableTopology E] IsCountablyCompact.isCompact
-- [FirstCountableTopology E] IsCountablyCompact.isSeqCompact
-- IsCountablyCompact.of_isClosed_subset
-- If A is countably compact, B⊆A, and B is closed, then B is countably compact


end
