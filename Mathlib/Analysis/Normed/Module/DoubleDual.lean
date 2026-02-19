/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# The double dual of a normed space

In this file we define the inclusion of a normed space into its double strong dual and prove
basic properties.

## Main definitions

* `NormedSpace.inclusionInDoubleDual` is the inclusion of a normed space in its double
  `StrongDual`, considered as a bounded linear map.
* `NormedSpace.inclusionInDoubleDualLi` is the same map as a linear isometry (for `𝕜 = ℝ` or
  `𝕜 = ℂ`).
* `NormedSpace.inclusionInDoubleDualWeak` is the canonical map from the weak space into the
  weak-star bidual.
* `NormedSpace.inclusionInDoubleDual_isEmbedding_weak` shows that `inclusionInDoubleDualWeak` is
  a topological embedding.
* `NormedSpace.inclusionInDoubleDual_homeomorph_weak` is the same map as a homeomorphism onto
  its range.
* `NormedSpace.instT2SpaceWeakSpace` shows the weak topology is Hausdorff (via Hahn–Banach).
* `NormedSpace.instBornologyWeakSpace` equips `WeakSpace` with the norm bornology from `X`.
* `NormedSpace.isCompact_closure` transfers compactness from the weak-star topology on the bidual
  back to the weak topology on `X` via Banach–Alaoglu.

## References

* [Conway, John B., A course in functional analysis][conway1990]

## Tags

double dual, inclusion, isometry, embedding
-/

@[expose] public section

noncomputable section

open Topology Bornology WeakDual

universe u v

namespace NormedSpace

section General

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The inclusion of a normed space in its double (topological) strong dual, considered
as a bounded linear map. -/
def inclusionInDoubleDual : E →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  ContinuousLinearMap.apply 𝕜 𝕜

@[simp]
theorem dual_def (x : E) (f : StrongDual 𝕜 E) : inclusionInDoubleDual 𝕜 E x f = f x :=
  rfl

theorem inclusionInDoubleDual_norm_eq :
    ‖inclusionInDoubleDual 𝕜 E‖ = ‖ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E)‖ :=
  ContinuousLinearMap.opNorm_flip _

theorem inclusionInDoubleDual_norm_le : ‖inclusionInDoubleDual 𝕜 E‖ ≤ 1 := by
  rw [inclusionInDoubleDual_norm_eq]
  exact ContinuousLinearMap.norm_id_le

theorem double_dual_bound (x : E) : ‖(inclusionInDoubleDual 𝕜 E) x‖ ≤ ‖x‖ := by
  simpa using ContinuousLinearMap.le_of_opNorm_le _ (inclusionInDoubleDual_norm_le 𝕜 E) x

end General

section BidualIsometry

variable (𝕜 : Type v) [RCLike 𝕜] {E : Type u}

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The inclusion of a normed space in its double strong dual is an isometry onto its image. -/
def inclusionInDoubleDualLi : E →ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  { inclusionInDoubleDual 𝕜 E with
    norm_map' x := by
      apply le_antisymm (double_dual_bound 𝕜 E x)
      obtain ⟨g, hg⟩ := exists_dual_vector'' 𝕜 x
      grw [← (inclusionInDoubleDual 𝕜 E x).unit_le_opNorm g hg.left]
      simp [hg.right] }

/-- If one controls the norm of every `f x`, then one controls the norm of `x`.
Compare `ContinuousLinearMap.opNorm_le_bound`. -/
theorem norm_le_dual_bound (x : E) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ f : StrongDual 𝕜 E, ‖f x‖ ≤ M * ‖f‖) : ‖x‖ ≤ M := by
  rw [← (inclusionInDoubleDualLi (E := E) 𝕜).norm_map x]
  exact ContinuousLinearMap.opNorm_le_bound _ hMp hM

end Seminormed

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem eq_zero_of_forall_dual_eq_zero {x : E} (h : ∀ f : StrongDual 𝕜 E, f x = (0 : 𝕜)) : x = 0 :=
  norm_le_zero_iff.mp (norm_le_dual_bound 𝕜 x le_rfl fun f => by simp [h f])

theorem eq_zero_iff_forall_dual_eq_zero (x : E) : x = 0 ↔ ∀ g : StrongDual 𝕜 E, g x = 0 :=
  ⟨fun hx => by simp [hx], fun h => eq_zero_of_forall_dual_eq_zero 𝕜 h⟩

/-- See also `geometric_hahn_banach_point_point`. -/
theorem eq_iff_forall_dual_eq {x y : E} : x = y ↔ ∀ g : StrongDual 𝕜 E, g x = g y := by
  rw [← sub_eq_zero, eq_zero_iff_forall_dual_eq_zero 𝕜 (x - y)]
  simp [sub_eq_zero]

end BidualIsometry

section Embedding

variable (𝕜 : Type*) [RCLike 𝕜] (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The canonical map from a normed space (with the weak topology) into the weak-star bidual.
This is `inclusionInDoubleDual` composed with `StrongDual.toWeakDual`, bundling the topology
change on both sides. -/
def inclusionInDoubleDualWeak (x : WeakSpace 𝕜 X) : WeakDual 𝕜 (StrongDual 𝕜 X) :=
  StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 X x)

/-- `inclusionInDoubleDualWeak` is a topological embedding from the weak topology to the weak-star
topology. That is, the canonical inclusion of a normed space into its double dual is an embedding
when the domain carries the weak topology and the codomain the weak-star topology.

The proof shows that both topologies on the domain are the topology of pointwise convergence
against `StrongDual 𝕜 X`. -/
theorem inclusionInDoubleDual_isEmbedding_weak :
    IsEmbedding (inclusionInDoubleDualWeak 𝕜 X) := by
  let evalWeakSpace : WeakSpace 𝕜 X → (StrongDual 𝕜 X → 𝕜) := fun x f => f x
  let evalWeakDual : WeakDual 𝕜 (StrongDual 𝕜 X) → (StrongDual 𝕜 X → 𝕜) := fun φ f => φ f
  have h_commute : evalWeakDual ∘ inclusionInDoubleDualWeak 𝕜 X = evalWeakSpace := by
    ext x f; rfl
  have h_inj : Function.Injective (inclusionInDoubleDualWeak 𝕜 X) :=
    StrongDual.toWeakDual.injective.comp (inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).injective
  have h_ind : IsInducing (inclusionInDoubleDualWeak 𝕜 X) := by
    constructor; symm
    calc TopologicalSpace.induced (inclusionInDoubleDualWeak 𝕜 X)
          (TopologicalSpace.induced evalWeakDual Pi.topologicalSpace)
        = TopologicalSpace.induced (evalWeakDual ∘ inclusionInDoubleDualWeak 𝕜 X)
            Pi.topologicalSpace := induced_compose
      _ = TopologicalSpace.induced evalWeakSpace Pi.topologicalSpace := by rw [h_commute]
  exact ⟨h_ind, h_inj⟩

/-- The inclusion of a normed space into its double dual, as a homeomorphism onto its range,
where the domain carries the weak topology and the codomain the weak-star topology. -/
def inclusionInDoubleDual_homeomorph_weak :
    WeakSpace 𝕜 X ≃ₜ Set.range (inclusionInDoubleDualWeak 𝕜 X) :=
  (inclusionInDoubleDual_isEmbedding_weak 𝕜 X).toHomeomorph

/-- The weak topology on a normed space over `RCLike` is T2 (Hausdorff). This follows from
Hahn–Banach: the continuous linear functionals separate points. -/
instance instT2SpaceWeakSpace : T2Space (WeakSpace 𝕜 X) :=
  (WeakBilin.isEmbedding (B := (topDualPairing 𝕜 X).flip) fun _ _ h =>
    (eq_iff_forall_dual_eq 𝕜).mpr fun g => LinearMap.ext_iff.mp h g).t2Space

/-- The norm bornology on `WeakSpace 𝕜 X`, inherited from `X`. -/
instance instBornologyWeakSpace : Bornology (WeakSpace 𝕜 X) :=
  inferInstanceAs (Bornology X)

/-- If `S` is bounded and the weak-star closure of its image under the canonical embedding into the
double dual lies in the range of that embedding, then `closure S` is compact in the weak topology.

This combines Banach–Alaoglu (compactness of bounded weak-star–closed sets) with the topological
embedding `inclusionInDoubleDual_isEmbedding_weak` to transfer compactness back to the weak
topology on `X`. -/
theorem isCompact_closure_of_bounded {S : Set (WeakSpace 𝕜 X)} (hb : IsBounded S)
    (hrange : closure (inclusionInDoubleDualWeak 𝕜 X '' S) ⊆
      Set.range (inclusionInDoubleDualWeak 𝕜 X)) :
    IsCompact (closure S) := by
  let homeo := inclusionInDoubleDual_homeomorph_weak 𝕜 X
  set K := closure (inclusionInDoubleDualWeak 𝕜 X '' S) with hK_def
  -- K is norm-bounded (weak-star closure of a bounded set stays bounded)
  have hK_bounded : IsBounded (StrongDual.toWeakDual ⁻¹' K) := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp
      ((inclusionInDoubleDual 𝕜 X).lipschitz.isBounded_image hb)
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨R, fun x hx => ?_⟩
    have : inclusionInDoubleDualWeak 𝕜 X '' S ⊆
        WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R := by
      rintro _ ⟨z, hz, rfl⟩
      simpa [inclusionInDoubleDualWeak, Metric.mem_closedBall, dist_zero_right] using
        hR ⟨z, hz, rfl⟩
    exact closure_minimal this (WeakDual.isClosed_closedBall 0 R) hx
  -- K is compact by Banach–Alaoglu
  have hK_compact : IsCompact K :=
    WeakDual.isCompact_of_bounded_of_closed hK_bounded isClosed_closure
  -- K lies in the range of the embedding, so pull back to a compact subset
  have hK_in_range : K ⊆ Set.range (inclusionInDoubleDualWeak 𝕜 X) := hrange
  have hK_pre_compact : IsCompact
      (Subtype.val ⁻¹' K : Set (Set.range (inclusionInDoubleDualWeak 𝕜 X))) := by
    rwa [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe,
      Set.inter_eq_left.mpr hK_in_range]
  -- Transfer through the homeomorphism to WeakSpace
  have hW_compact : IsCompact (homeo.symm ''
      (Subtype.val ⁻¹' K : Set (Set.range (inclusionInDoubleDualWeak 𝕜 X)))) :=
    hK_pre_compact.image homeo.symm.continuous
  refine hW_compact.of_isClosed_subset isClosed_closure
    (closure_minimal ?_ hW_compact.isClosed)
  -- S maps into homeo.symm '' (Subtype.val ⁻¹' K)
  intro z hz
  exact ⟨⟨inclusionInDoubleDualWeak 𝕜 X z, z, rfl⟩,
    subset_closure ⟨z, hz, rfl⟩,
    (inclusionInDoubleDual_isEmbedding_weak 𝕜 X).toHomeomorph_symm_apply _⟩

end Embedding

end NormedSpace
