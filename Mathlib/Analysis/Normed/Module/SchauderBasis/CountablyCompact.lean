/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Defs.Sequences

@[expose] public section

noncomputable section

open Set Filter Topology

def IsCountablyCompact {E : Type*} [TopologicalSpace E] (A : Set E) : Prop :=
  ∀ x : ℕ → E, (∀ n, x n ∈ A) → ∃ a ∈ A, MapClusterPt a atTop x

theorem IsCompact_IsCountablyCompact {E : Type*} [TopologicalSpace E] {A : Set E} :
    IsCompact A → IsCountablyCompact A := by
  intro hA x h_mem
  exact hA (Filter.le_principal_iff.mpr (Filter.mem_map.mpr (Filter.Eventually.of_forall h_mem)))

theorem IsSeqCompact_IsCountablyCompact {E : Type*} [TopologicalSpace E] {A : Set E} :
    IsSeqCompact A → IsCountablyCompact A := by
  intro hA x h_mem
  obtain ⟨a, ha_mem, φ, hφ_mono, hφ_tendsto⟩ := hA h_mem
  exact ⟨a, ha_mem, (hφ_tendsto.mapClusterPt).of_comp hφ_mono.tendsto_atTop⟩
