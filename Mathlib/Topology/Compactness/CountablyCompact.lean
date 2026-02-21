/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Defs.Sequences
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Topology.Separation.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Topology.Bases

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
    have hmem (n : ℕ) : (s n ∩ A).Nonempty :=
      Filter.nonempty_of_mem (Filter.inter_mem (hs.mem n) (le_principal_iff.mp hle))
    choose x hx using hmem
    obtain ⟨a, ha, hac⟩ := hA x (fun n => (hx n).2)
    exact ⟨a, ha, ClusterPt.mono hac (hs.tendsto (fun n => (hx n).1))⟩
  · intro h x hx
    exact h (map x atTop) (le_principal_iff.mpr (mem_map.mpr (Eventually.of_forall hx)))

/-- A point `a` is a cluster point of the sequence `x` if and only if `a` belongs to the closure
of every tail `x '' {n | i ≤ n}`. -/
theorem mapClusterPt_atTop_iff_forall_mem_closure {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {x : ι → E} {a : E} :
    MapClusterPt a atTop x ↔ ∀ i, a ∈ closure (x '' Ici i) :=
  show ClusterPt a (map x atTop) ↔ _ by
    simp only [(atTop_basis.map x).clusterPt_iff_forall_mem_closure, true_implies]

private theorem isCountablyCompact_elim_finite_subcover_nat {A : Set E}
    (hA : IsCountablyCompact A) {U : ℕ → Set E} (hUo : ∀ i, IsOpen (U i))
    (hAU : A ⊆ ⋃ i, U i) : ∃ t : Finset ℕ, A ⊆ ⋃ i ∈ t, U i := by
  by_contra h
  push_neg at h
  choose x hxA hxU using fun n => Set.not_subset.mp (h (Finset.range (n + 1)))
  obtain ⟨a, haA, hac⟩ := hA x hxA
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hAU haA)
  have : ∀ᶠ n in atTop, x n ∉ U k :=
    Eventually.mono (Ici_mem_atTop k) fun n hn hxn =>
      hxU n (mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)) hxn)
  exact hac.frequently ((hUo k).mem_nhds hk) this

theorem isCountablyCompact_iff_countable_open_cover {A : Set E} :
    IsCountablyCompact A ↔
      ∀ (U : ℕ → Set E), (∀ i, IsOpen (U i)) → A ⊆ ⋃ i, U i →
        ∃ t : Finset ℕ, A ⊆ ⋃ i ∈ t, U i := by
  constructor
  · exact fun hA U => isCountablyCompact_elim_finite_subcover_nat hA
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
    let m := t.sup id
    obtain ⟨j, hjt, hjV⟩ := mem_iUnion₂.mp (ht (hx m))
    have hxmV : x m ∈ V m := hVmono (Finset.le_sup hjt) hjV
    exact hxmV (subset_closure ⟨m, mem_Ici.mpr le_rfl, rfl⟩)

/-- A countably compact set has a finite subcover for any countable open cover. -/
theorem IsCountablyCompact.elim_finite_subcover {A : Set E} (hA : IsCountablyCompact A)
    {ι : Type*} [Countable ι] {U : ι → Set E} (hUo : ∀ i, IsOpen (U i))
    (hAU : A ⊆ ⋃ i, U i) : ∃ t : Finset ι, A ⊆ ⋃ i ∈ t, U i := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨∅, ?_⟩
    rw [iUnion_of_empty] at hAU
    exact hAU.trans (empty_subset _)
  · obtain ⟨e, he⟩ := exists_surjective_nat ι
    obtain ⟨s, hs⟩ := isCountablyCompact_elim_finite_subcover_nat hA
      (fun n => hUo (e n)) (by rwa [he.iUnion_comp])
    exact ⟨s.image e, hs.trans (iUnion₂_subset fun n hn =>
      subset_biUnion_of_mem (Finset.mem_image_of_mem e hn))⟩

theorem IsCompact.IsCountablyCompact {A : Set E} (hA : IsCompact A) : IsCountablyCompact A :=
  fun _ h_mem => hA (le_principal_iff.2 (mem_map.2 (Eventually.of_forall h_mem)))

theorem IsSeqCompact.IsCountablyCompact {A : Set E} (hA : IsSeqCompact A) :
    IsCountablyCompact A := by
  intro x h_mem
  obtain ⟨a, ha_mem, φ, hφ_mono, hφ_tendsto⟩ := hA h_mem
  exact ⟨a, ha_mem, (hφ_tendsto.mapClusterPt).of_comp hφ_mono.tendsto_atTop⟩


theorem IsCountablyCompact.exists_accPt_of_infinite {A : Set E}
    (hA : IsCountablyCompact A) {B : Set E} (hBA : B ⊆ A) (hB : B.Infinite) :
    ∃ a ∈ A, AccPt a (𝓟 B) := by
  let f := hB.natEmbedding B
  let x : ℕ → E := fun n => ↑(f n)
  have hxA : ∀ n, x n ∈ A := fun n => hBA (f n).prop
  have hxB : ∀ n, x n ∈ B := fun n => (f n).prop
  have hx_inj : Function.Injective x := Subtype.val_injective.comp f.injective
  obtain ⟨a, haA, hac⟩ := hA x hxA
  refine ⟨a, haA, accPt_iff_clusterPt.mpr (ClusterPt.mono hac ?_)⟩
  rw [le_inf_iff]
  exact ⟨le_principal_iff.mpr (mem_map.mpr
    (Nat.cofinite_eq_atTop ▸ ((finite_singleton a).preimage
      (injOn_of_injective hx_inj)).compl_mem_cofinite)),
    le_principal_iff.mpr (mem_map.mpr (Eventually.of_forall hxB))⟩

theorem isCountablyCompact_iff_infinite_subset_has_accPt [T1Space E] {A : Set E} :
    IsCountablyCompact A ↔ ∀ B ⊆ A, B.Infinite → ∃ a ∈ A, AccPt a (𝓟 B) := by
  constructor
  · exact fun hA B hBA hB => hA.exists_accPt_of_infinite hBA hB
  · intro h x hx
    by_cases hfin : (Set.range x).Finite
    · -- Finite range: pigeonhole gives a value repeated infinitely often
      haveI := hfin.to_subtype
      obtain ⟨⟨a, ha_range⟩, ha_inf⟩ :=
        Finite.exists_infinite_fiber (Set.rangeFactorization x)
      rw [Set.infinite_coe_iff] at ha_inf
      simp only [Set.preimage, Set.mem_singleton_iff, Set.rangeFactorization,
        Subtype.mk.injEq] at ha_inf
      refine ⟨a, range_subset_iff.mpr hx ha_range, ?_⟩
      rw [mapClusterPt_atTop_iff_forall_mem_closure]
      intro i
      obtain ⟨n, hxn, hin⟩ :=
        ((Nat.frequently_atTop_iff_infinite.mpr ha_inf).and_eventually (Ici_mem_atTop i)).exists
      exact subset_closure ⟨n, hin, hxn⟩
    · -- Infinite range: use hypothesis and T1 to get cluster point
      rw [Set.not_finite] at hfin
      obtain ⟨a, haA, hacc⟩ := h (Set.range x) (range_subset_iff.mpr hx) hfin
      refine ⟨a, haA, ?_⟩
      rw [mapClusterPt_atTop_iff_forall_mem_closure]
      intro i
      rw [mem_closure_iff_nhds]
      intro U hU
      suffices h_inf : {n | x n ∈ U}.Infinite by
        obtain ⟨n, hn, hni⟩ :=
          ((Nat.frequently_atTop_iff_infinite.mpr h_inf).and_eventually
            (Ici_mem_atTop i)).exists
        exact ⟨x n, ⟨hn, n, hni, rfl⟩⟩
      suffices h_inf_inter : (U ∩ Set.range x).Infinite by
        exact (h_inf_inter.preimage (inter_subset_right)).mono
          (preimage_mono inter_subset_left)
      by_contra h_fin
      rw [Set.not_infinite] at h_fin
      set F := (U ∩ Set.range x) \ {a} with hF_def
      have hF_closed : IsClosed F := (h_fin.subset diff_subset).isClosed
      have haF : a ∉ F := fun hf => hf.2 rfl
      have hacc_freq : ∃ᶠ y in 𝓝 a, y ≠ a ∧ y ∈ Set.range x :=
        accPt_iff_frequently.mp hacc
      obtain ⟨y, ⟨hya, hyr⟩, hyU, hyFc⟩ :=
        (hacc_freq.and_eventually
          (Filter.inter_mem hU (hF_closed.isOpen_compl.mem_nhds (mem_compl haF)))).exists
      exact hyFc ⟨⟨hyU, hyr⟩, hya⟩

theorem IsCountablyCompact.isCompact [SecondCountableTopology E] {A : Set E}
    (hA : IsCountablyCompact A) : IsCompact A := by
  classical
  apply isCompact_of_finite_subcover
  intro ι U hUo hAU
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  haveI : Countable ↥T := hTc.to_subtype
  have hAT : A ⊆ ⋃ i ∈ T, U i := by rw [hTeq]; exact hAU
  rw [Set.biUnion_eq_iUnion] at hAT
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun i => hUo _) hAT
  exact ⟨t.image Subtype.val, by rwa [Finset.set_biUnion_finset_image]⟩


-- [FirstCountableTopology E] IsCountablyCompact.isSeqCompact
-- IsCountablyCompact.of_isClosed_subset


end
