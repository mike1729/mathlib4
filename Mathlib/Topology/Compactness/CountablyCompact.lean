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
