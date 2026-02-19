/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Defs.Sequences

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

theorem IsCompact.IsCountablyCompact {A : Set E} (hA : IsCompact A) : IsCountablyCompact A :=
  fun _ h_mem => hA (le_principal_iff.2 (mem_map.2 (Eventually.of_forall h_mem)))

theorem IsSeqCompact.IsCountablyCompact {A : Set E} (hA : IsSeqCompact A) :
    IsCountablyCompact A := by
  intro x h_mem
  obtain ⟨a, ha_mem, φ, hφ_mono, hφ_tendsto⟩ := hA h_mem
  exact ⟨a, ha_mem, (hφ_tendsto.mapClusterPt).of_comp hφ_mono.tendsto_atTop⟩

end
