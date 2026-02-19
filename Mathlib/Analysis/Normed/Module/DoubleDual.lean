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
* `NormedSpace.inclusionInDoubleDual_isEmbedding_weak` shows that the inclusion is an embedding
  from the weak topology to the weak-star topology.
* `NormedSpace.inclusionInDoubleDual_homeomorph_weak` is the same map as a homeomorphism onto
  its range.

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

/-- The map `WeakSpace 𝕜 X → WeakDual 𝕜 (StrongDual 𝕜 X)` induced by `inclusionInDoubleDual`
is a topological embedding. That is, the canonical inclusion of a normed space into its double dual
is an embedding when the domain carries the weak topology and the codomain the weak-star topology.

The proof shows that both topologies on the domain are the topology of pointwise convergence
against `StrongDual 𝕜 X`. -/
theorem inclusionInDoubleDual_isEmbedding_weak :
    IsEmbedding (fun x : WeakSpace 𝕜 X => StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 X x)) := by
  let ι := fun x : WeakSpace 𝕜 X => StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 X x)
  let evalWeakSpace : WeakSpace 𝕜 X → (StrongDual 𝕜 X → 𝕜) := fun x f => f x
  let evalWeakDual : WeakDual 𝕜 (StrongDual 𝕜 X) → (StrongDual 𝕜 X → 𝕜) := fun φ f => φ f
  have h_commute : evalWeakDual ∘ ι = evalWeakSpace := by ext x f; rfl
  have h_inj : Function.Injective ι :=
    StrongDual.toWeakDual.injective.comp (inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).injective
  have h_ind : IsInducing ι := by
    constructor; symm
    calc TopologicalSpace.induced ι (TopologicalSpace.induced evalWeakDual Pi.topologicalSpace)
        = TopologicalSpace.induced (evalWeakDual ∘ ι) Pi.topologicalSpace := induced_compose
      _ = TopologicalSpace.induced evalWeakSpace Pi.topologicalSpace := by rw [h_commute]
  exact ⟨h_ind, h_inj⟩

/-- The inclusion of a normed space into its double dual, as a homeomorphism onto its range,
where the domain carries the weak topology and the codomain the weak-star topology. -/
def inclusionInDoubleDual_homeomorph_weak :
    WeakSpace 𝕜 X ≃ₜ Set.range (fun x : WeakSpace 𝕜 X =>
      StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 X x)) :=
  (inclusionInDoubleDual_isEmbedding_weak 𝕜 X).toHomeomorph

end Embedding

end NormedSpace
