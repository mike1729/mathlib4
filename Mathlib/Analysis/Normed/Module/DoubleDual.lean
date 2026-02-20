/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.WeakSpace

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
* `NormedSpace.inclusionInDoubleDualWeak_isEmbedding` shows that `inclusionInDoubleDualWeak` is
  a topological embedding.
* `NormedSpace.inclusionInDoubleDualWeak_homeomorph` is the same map as a homeomorphism onto
  its range.
* `NormedSpace.isCompact_closure_of_isBounded` transfers compactness from the weak-star topology
  on the bidual back to the weak topology on `X` via Banach–Alaoglu.

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

end BidualIsometry

section Embedding

variable (𝕜 : Type*) [RCLike 𝕜] (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The canonical map from a normed space (with the weak topology) into the weak-star bidual.
This is `inclusionInDoubleDual` composed with `StrongDual.toWeakDual`, bundling the topology
change on both sides. -/
def inclusionInDoubleDualWeak (x : WeakSpace 𝕜 X) : WeakDual 𝕜 (StrongDual 𝕜 X) :=
  StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 X x)

/-- The canonical embedding into the weak-star bidual evaluates to `f x`. -/
@[simp]
theorem inclusionInDoubleDualWeak_apply (x : WeakSpace 𝕜 X) (f : StrongDual 𝕜 X) :
    (inclusionInDoubleDualWeak 𝕜 X x) f = f x :=
  rfl

/-- `inclusionInDoubleDualWeak` is inducing: the weak topology on `X` coincides with the topology
pulled back from the weak-star topology on the bidual. Both are the topology of pointwise
convergence against `StrongDual 𝕜 X`. -/
theorem inclusionInDoubleDualWeak_isInducing :
    IsInducing (inclusionInDoubleDualWeak 𝕜 X) where
  eq_induced := by
    change _ = TopologicalSpace.induced (inclusionInDoubleDualWeak 𝕜 X)
      (TopologicalSpace.induced
        (fun (φ : WeakDual 𝕜 (StrongDual 𝕜 X)) f => φ f) Pi.topologicalSpace)
    rw [induced_compose]
    rfl

/-- `inclusionInDoubleDualWeak` is a topological embedding from the weak topology to the weak-star
topology. -/
theorem inclusionInDoubleDualWeak_isEmbedding :
    IsEmbedding (inclusionInDoubleDualWeak 𝕜 X) where
  toIsInducing := inclusionInDoubleDualWeak_isInducing 𝕜 X
  injective := StrongDual.toWeakDual.injective.comp
    (inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).injective

/-- The inclusion of a normed space into its double dual, as a homeomorphism onto its range,
where the domain carries the weak topology and the codomain the weak-star topology. -/
def inclusionInDoubleDualWeak_homeomorph :
    WeakSpace 𝕜 X ≃ₜ Set.range (inclusionInDoubleDualWeak 𝕜 X) :=
  (inclusionInDoubleDualWeak_isEmbedding 𝕜 X).toHomeomorph

/-- If `S` is bounded and the weak-star closure of its image under the canonical embedding into the
double dual lies in the range of that embedding, then `closure S` is compact in the weak topology.

This combines Banach–Alaoglu (compactness of bounded weak-star–closed sets) with the topological
embedding `inclusionInDoubleDualWeak_isEmbedding` to transfer compactness back to the weak
topology on `X`. -/
theorem isCompact_closure_of_isBounded {S : Set (WeakSpace 𝕜 X)} (hb : IsBounded S)
    (hrange : closure (inclusionInDoubleDualWeak 𝕜 X '' S) ⊆
      Set.range (inclusionInDoubleDualWeak 𝕜 X)) :
    IsCompact (closure S) := by
  rw [(inclusionInDoubleDualWeak_isInducing 𝕜 X).closure_eq_preimage_closure_image]
  apply (inclusionInDoubleDualWeak_isInducing 𝕜 X).isCompact_preimage' _ hrange
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp
    ((inclusionInDoubleDual 𝕜 X).lipschitz.isBounded_image hb)
  refine (WeakDual.isCompact_closedBall (𝕜 := 𝕜) (E := StrongDual 𝕜 X) 0 R).of_isClosed_subset
    isClosed_closure (closure_minimal ?_ (WeakDual.isClosed_closedBall 0 R))
  rintro _ ⟨z, hz, rfl⟩
  exact hR ⟨z, hz, rfl⟩

end Embedding

end NormedSpace
