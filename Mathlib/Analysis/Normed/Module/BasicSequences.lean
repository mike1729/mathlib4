/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Basic Sequences in Banach Spaces
-/

noncomputable section

open Submodule Set WeakDual Metric

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/--
A sequence `e` is a **Basic Sequence** if it forms a Schauder Basis for its closed linear span.
-/
def IsBasicSequence (𝕜 : Type*) {X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) : Prop :=
  let Y := (span 𝕜 (range e)).topologicalClosure
  let e_Y : ℕ → Y := fun n ↦ ⟨e n,
    Submodule.le_topologicalClosure _ (subset_span (mem_range_self n))⟩
  Nonempty (SchauderBasis 𝕜 e_Y)

namespace BasicSequences

-- variable (𝕜 : Type*) {X : Type*} [NontriviallyNormedField 𝕜]
--     [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {e : ℕ → X}

/-- Every Schauder Basis of the whole space `X` is a basic sequence. -/
theorem isBasicSequence_self (b : SchauderBasis 𝕜 e) : IsBasicSequence 𝕜 e := by
  -- rw [IsBasicSequence]
  -- let Y := (span 𝕜 (range e)).topologicalClosure
  -- have h_dense : Y = ⊤ := by
  --   rw [eq_top_iff']
  --   intro x
  --   -- Proof sketch: The basis expansion converges, so x is in the closure of the span.
  --   exact mem_closure_of_tendsto (b.basis_expansion x)
  --     (eventually_of_forall (fun n ↦ sum_mem (fun i _ ↦ smul_mem _ _ (subset_span (mem_range_self i)))))
  -- -- We construct the basis for Y by restricting b.
  -- -- (Technical construction omitted for brevity, asserting existence).
  -- use ?_
  sorry -- Standard coercion of basis to the top submodule.

/-- The **Basis Constant** of a basic sequence. -/
noncomputable def basicSequenceConstant (he : IsBasicSequence 𝕜 e) : ℝ :=
  (Classical.choice he).basisConstant



/-- A sequence satisfies the **Grünblum Condition** if the norms of the projections
onto the span of its first `n` elements are uniformly bounded. -/
def SatisfiesGrunblumCondition (𝕜 : Type*) {X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) : Prop :=
  ∃ K, 1 ≤ K ∧ ∀ (n m : ℕ) (a : ℕ → 𝕜), m ≤ n →
    ‖∑ i ∈ Finset.range m, a i • e i‖ ≤ K * ‖∑ i ∈ Finset.range n, a i • e i‖

/-- A basic sequence implies the Grünblum inequality holds for its basis constant. -/
theorem grunblum_of_basic (he : IsBasicSequence 𝕜 e) : SatisfiesGrunblumCondition 𝕜 e := by
    sorry


lemma linear_independet_of_grunblum (h_grunblum : SatisfiesGrunblumCondition 𝕜 e)
    (h_nz : ∀ n, e n ≠ 0) : LinearIndependent 𝕜 e := by
  rcases h_grunblum with ⟨K, hK_ge_1, hK⟩
  rw [linearIndependent_iff']
  intro s g h_sum i hi_s
  -- 1. Construct global coefficients 'c' that match 'g' on s and are 0 otherwise
  let c := fun j => if j ∈ s then g j else 0
  let N := s.sup id + 1

  -- 2. Show the sum over a large range N is zero (matching the hypothesis)
  have h_total : ∑ j ∈ Finset.range N, c j • e j = 0 := by
    rw [← h_sum]
    have h_ss : s ⊆ Finset.range N := by
      intro j hj
      simp only [Finset.mem_range]
      exact lt_of_le_of_lt (Finset.le_sup hj) (Nat.lt_succ_self _)
    rw [← Finset.sum_subset h_ss]
    · rw [h_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp [c, hj]
    · intro j _ h_notin
      simp [c, h_notin]
    -- apply (smul_eq_zero_iff_left (h_nz j)).mp



  -- 3. Use Grünblum to show the term at 'i' is 0 (diff of two zero partial sums)
  have h_term : c i • e i = 0 := by
    -- The term at i is S_{i+1} - S_i
    rw [← Finset.sum_range_succ_sub_sum (fun j ↦ c j • e j)]
    let hK_N := hK (n := N) (a := c)
    rw [h_total, norm_zero, mul_zero] at hK_N
    have : i + 1 ≤ N := by
      dsimp only [N]
      apply Nat.succ_le_succ
      exact Finset.le_sup hi_s (f := id)

    rw [norm_le_zero_iff.mp (hK_N (i + 1) this),
      norm_le_zero_iff.mp (hK_N i ((Nat.le_succ i).trans this)), sub_zero]

  -- 4. Conclude g i = 0
  simp only [c, if_pos hi_s] at h_term
  exact (smul_eq_zero.mp h_term).resolve_right (h_nz i)
/--
**The Grünblum Criterion**:
If a sequence satisfies the Grünblum condition (bounded projections on the span),
and the elements are non-zero, then it is a Basic Sequence.
-/
theorem isBasicSequence_of_grunblum [CompleteSpace X]
    (h_grunblum : SatisfiesGrunblumCondition 𝕜 e)
    (h_nz : ∀ n, e n ≠ 0) : IsBasicSequence 𝕜 e := by

  have h_indep := linear_independet_of_grunblum h_grunblum h_nz
  rcases h_grunblum with ⟨K, hK_ge_1, hK⟩

  -- 1. Prove Linear Independence
  -- The Grünblum condition implies that if a finite combination is 0,
  -- its partial sums must have norm 0.

  let S := Submodule.span 𝕜 (Set.range e)
  let Y := S.topologicalClosure

  let b_S := Module.Basis.span h_indep
  have hbS : ∀ n, b_S n = e n := by
    intro n
    rw [Module.Basis.span_apply h_indep n]
  let e_Y' : ℕ → Y := fun n => ⟨e n, Submodule.subset_span (Set.mem_range_self n) |> Submodule.le_topologicalClosure S⟩
  let e_Y : ℕ → Y := Submodule.inclusion (Submodule.le_topologicalClosure S) ∘ b_S
  have heY_eq : ∀ n, e_Y n = e_Y' n := sorry

  -- 3. Define Projections on the dense span S
  let P_span (k : ℕ) : S →ₗ[𝕜] S := b_S.constr 𝕜 (fun i => if i < k then b_S i else 0)

  have h_P_span_apply (k : ℕ) (x : S) :
      P_span k x = ∑ i ∈ Finset.range k, b_S.repr x i • b_S i := by
    rw [Module.Basis.constr_apply, Finsupp.sum]
    refine Finset.sum_congr_of_eq_on_inter ?_ ?_ ?_ <;> intro i h1 h2
    · -- Case: i ∈ supp \ range k
      rw [if_neg (by simpa using h2), smul_zero]
    · -- Case: i ∈ range k \ supp
      rw [Finsupp.notMem_support_iff.mp h2, zero_smul]
    · -- Case: i ∈ supp ∩ range k
      rw [if_pos (by simpa using h2)]

    -- -- 3. Express P_span k x as a sum in X up to k
  have h_P_span_bound (k : ℕ) (x : S) : ‖P_span k x‖ ≤ K * ‖x‖ := by
    let a := b_S.repr x
    let N := max k (a.support.sup id + 1)
    have hk_le_N : k ≤ N := le_max_left _ _

    -- 1. Express x as a sum in X
    have hx : (x : X) = ∑ i ∈ Finset.range N, (b_S.repr x) i • b_S i := by
      nth_rw 1 [← b_S.linearCombination_repr x]
      rw [Finsupp.linearCombination_apply]
      rw [← h_P_span_apply N x]
      dsimp only [P_span]
      rw [b_S.constr_apply, Finsupp.sum_congr]
      intro i hi
      rw [if_pos]

      calc i
        _ ≤ (b_S.repr x).support.sup id   := Finset.le_sup hi (f := id)
        _ < (b_S.repr x).support.sup id + 1 := Nat.lt_succ_self _
        _ ≤ N                    := le_max_right _ _

    -- 3. Apply the Grünblum inequality
    rw [← norm_coe, ← norm_coe, hx,  h_P_span_apply]
    simp_rw [Submodule.coe_sum, Submodule.coe_smul, hbS]
    exact hK N k (b_S.repr x) hk_le_N

  -- 4. Extend to Y
  let P_SS (k : ℕ) : S →L[𝕜] S := LinearMap.mkContinuous (P_span k) K (h_P_span_bound k)
  let ι : S →L[𝕜] Y := LinearMap.mkContinuous
    (Submodule.inclusion (Submodule.le_topologicalClosure S)) 1 (fun x ↦ by simp only [AddSubgroupClass.coe_norm, Submodule.coe_inclusion, one_mul, le_refl])

  -- 2. Define P directly by extending the map (S → Y).
  let P (k : ℕ) : Y →L[𝕜] Y :=
    (LinearMap.mkContinuous (ι.toLinearMap.comp (P_span k)) K (by
      intro x
      -- The norm in Y is the same as in S, so the bound K still holds
      simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk,
                  Submodule.inclusion_apply, Submodule.coe_norm]
        using h_P_span_bound k x)
    ).extend ι
  have h_dense : DenseRange ι := (denseRange_inclusion_iff ?_).mpr ?_

  have h_uniind : IsUniformInducing ι := by
    apply Isometry.isUniformInducing
    apply AddMonoidHomClass.isometry_of_norm
    intro x
    rfl
  -- Properties subsetof the extended projection
  have h_P_eq_on_S (k : ℕ) (x : S) : P k (ι x)  = ι (P_span k x) := by
    -- The extension agrees with the original map on the dense subspace
    rw [ContinuousLinearMap.extend_eq]
    · dsimp only [LinearMap.mkContinuous_apply, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply]
    · exact h_dense -- Density of S in Y
    · exact h_uniind -- isuniformly_continuous


  -- 5. Verify Schauder Basis Conditions
  have h0 : P 0 = 0 := by
    have : P_span 0 = 0 := by
      ext x
      simp_rw [h_P_span_apply, Finset.range_zero, Finset.sum_empty]
      rfl
    apply ContinuousLinearMap.extend_unique
    · exact h_dense -- S is dense in Y
    · exact h_uniind -- The inclusion is uniformly inducing
    ext x
    -- 3. Simplify P 0 on S (it is the zero map because k=0)
    simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.zero_apply, ZeroMemClass.coe_zero,
    LinearMap.mkContinuous_apply, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply]
    -- 4. P_span 0 x is 0
    rw [h_P_span_apply]
    simp only [Finset.range_zero, Finset.sum_empty, map_zero]
    rfl



    -- apply ContinuousLinearMap.opNorm_ext; refine ContinuousLinearMap.dense_range_coe (Submodule.topologicalClosure_subtype S) ?_
    -- intro x
    -- rw [ContinuousLinearMap.zero_apply, h_P_eq_on_S]
    -- simp [P_span, Basis.constr_basis, if_neg (Nat.not_lt_zero _)]
    -- apply LinearMap.map_zero

  have hdim (n : ℕ) : Module.finrank 𝕜 (LinearMap.range (P n).toLinearMap) = n := by
    -- The range of P n is the closure of the range of P_span n.
    -- But range of P_span n is finite dimensional (span of e_0...e_{n-1}), so it is closed.
    -- Thus range P n = range P_span n.
    -- Rank is n because e_i are linearly independent.
    sorry -- Standard rank argument using linearity and density

  have hcomp (n m : ℕ) (y : Y) : P n (P m y) = P (min n m) y := by
    -- Verify on dense set S
    refine ContinuousLinearMap.dense_range_coe (Submodule.topologicalClosure_subtype S) ?_ y
    intro x
    simp only [h_P_eq_on_S]
    -- P_span maps S to S, so P m x ∈ S.
    rw [h_P_eq_on_S]
    -- Now check composition on P_span
    apply b_S.ext; intro i
    simp only [LinearMap.comp_apply, P_span, Basis.constr_basis]
    split_ifs <;> simp

  have hlim (y : Y) : Tendsto (fun n ↦ P n y) atTop (𝓝 y) := by
    -- Use Banach-Steinhaus / Density argument
    -- 1. Uniformly bounded: ‖P n‖ ≤ K
    have h_unif : ∀ n, ‖P n‖ ≤ K := by
      intro n
      rw [ContinuousLinearMap.opNorm_extend]
      apply ContinuousLinearMap.opNorm_le_bound _ (le_trans (by norm_num) (h_grunblum.choose_spec.1)) (h_P_span_bound n)

    -- 2. Convergence on dense subset S
    have h_conv_S (x : S) : Tendsto (fun n ↦ P n x) atTop (𝓝 x) := by
      simp_rw [h_P_eq_on_S]
      -- For x in span, x is a finite sum. For large n, P_span n x = x.
      obtain ⟨supp, hx⟩ := b_S.mem_span x
      let N := supp.sup id + 1
      rw [tendsto_atTop_eq_eventually_eq (x := (x:Y)) (i₀ := N)]
      intro n hn
      rw [h_P_span_apply]
      -- Sum is actually x because n covers support
      conv_rhs => rw [← hx]
      apply Finset.sum_subset
      · intro i hi; simp only [Finset.mem_range]; apply lt_of_le_of_lt (Finset.le_sup hi) hn
      · intro i _ hi; simp [Basis.repr_support, hi]

    -- 3. Combine
    apply tendsto_of_uniform_bound_of_dense (h_unif) (fun x ↦ h_conv_S x) (Submodule.dense_topologicalClosure S)

  -- Conclusion
  use SchauderBasis.basis_of_canonical_projections h0 hdim hcomp hlim

lemma perturbation_finite_dimensional {S : Set (StrongDual 𝕜 X)}
    (h_weak_star : (0 : WeakDual 𝕜 X) ∈ closure (StrongDual.toWeakDual '' S))
    (h_norm : (0 : StrongDual 𝕜 X) ∉ closure S)
    (E : Subspace 𝕜 (StrongDual 𝕜 X)) (he: Nontrivial E)
    (hefind : FiniteDimensional 𝕜 E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ S, ∀ (e : E) (c : 𝕜), ‖(e : StrongDual 𝕜 X) + c • x‖ ≥ (1 - ε) * ‖e‖ := by
  -- 0. Handle trivial ε case
  rcases le_or_gt 1 ε with hε1 | hε1
  · -- If ε ≥ 1, any x ∈ S works
    obtain ⟨-, -, x, hxS, -⟩ := mem_closure_iff.mp h_weak_star _ isOpen_univ trivial
    use x, hxS
    intro e c
    -- Since ε ≥ 1, (1-ε) ≤ 0. The inequality holds trivially as LHS ≥ 0 and RHS ≤ 0.
    refine le_trans ?_ (norm_nonneg _)
    apply mul_nonpos_of_nonpos_of_nonneg
    · linarith [hε1]
    · exact norm_nonneg _

  -- 1. Setup constants based on distance to S
  obtain ⟨δ, hδ, hδS⟩ := Metric.exists_real_pos_lt_infEDist_of_notMem_closure h_norm
  let M := 2 / δ
  let γ := ε * δ / 4

  have h_norm_S : ∀ x ∈ S, δ ≤ ‖x‖ := by
    intro x hx
    have : ENNReal.ofReal δ < edist (0 : StrongDual 𝕜 X) x :=
      lt_of_lt_of_le hδS (Metric.infEDist_le_edist_of_mem hx)
    rw [edist_dist, dist_zero_left] at this
    exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg x)).mp this.le
  -- 2. Use compactness of the sphere in E to find a finite "test set" F ⊂ X
  let sphere := Metric.sphere (0 : E) 1
  -- Define the open sets covering the sphere, indexed by the unit ball of vectors X.
  let U (v : {v : X // ‖v‖ ≤ 1}) : Set E := {e | 1 - ε / 2 < ‖(e : StrongDual 𝕜 X) v‖}

  have h_cover : sphere ⊆ ⋃ v, U v := by
    intro e he
    rw [mem_sphere_zero_iff_norm] at he
    -- We have ‖e‖ = 1 and ε > 0, so 1 - ε/2 < ‖e‖
    have h_lt : 1 - ε / 2 < ‖(e : StrongDual 𝕜 X)‖ := by
      rw [norm_coe, he]
      linarith
    -- Find a vector v with ||v|| ≤ 1 that "witnesses" the norm of e
    obtain ⟨v, hv, hv_val⟩ := ContinuousLinearMap.exists_lt_apply_of_lt_opNorm (e : StrongDual 𝕜 X) h_lt
    exact Set.mem_iUnion.mpr ⟨⟨v, hv.le⟩, hv_val⟩

  have h_open (v : {v : X // ‖v‖ ≤ 1}) : IsOpen (U v) := by
    have : Continuous fun (e : E) => (e : StrongDual 𝕜 X) v.val :=
      (ContinuousLinearMap.apply 𝕜 𝕜 v.val).continuous.comp continuous_subtype_val
    exact isOpen_Ioi.preimage (Continuous.norm this)

  -- Extract finite subcover
  obtain ⟨F, hF_cover⟩ := (isCompact_sphere (0 : E) 1).elim_finite_subcover U h_open h_cover

  -- 3. Find perturbation x ∈ S small on F (using weak* closure)
  let W := {w : WeakDual 𝕜 X | ∀ v ∈ F, ‖w v‖ < γ}
  have hW_open : IsOpen W := by
    rw [show W = ⋂ v ∈ F, {w | ‖w v‖ < γ} by ext; simp [W]]
    apply isOpen_biInter_finset
    intro v _
    refine isOpen_lt (continuous_norm.comp (WeakDual.eval_continuous (v : X))) continuous_const
  have hγ : 0 < γ := by
    dsimp [γ]
    nlinarith [hε, hδ]

  have hW0 : (0 : WeakDual 𝕜 X) ∈ W := by
    simp only [W, Set.mem_setOf_eq]
    intro v _
    rw [ContinuousLinearMap.zero_apply, norm_zero]
    exact hγ

  -- Use weak-star density to find x ∈ S that is small on F
  obtain ⟨_, hwW, ⟨x, hxS, rfl⟩⟩ : ∃ w ∈ W, ∃ x ∈ S, StrongDual.toWeakDual x = w :=
      (_root_.mem_closure_iff).mp h_weak_star W hW_open hW0

  -- 4. Verify the inequality
  refine ⟨x, hxS, fun e c ↦ ?_⟩
  rcases eq_or_ne e 0 with rfl | he_ne; · simp [norm_nonneg]
  -- Scale e to the sphere
  let e_norm := ‖e‖
  let e' : E := (e_norm⁻¹ : 𝕜) • e
  have he'_norm : ‖e'‖ = 1 := norm_smul_inv_norm he_ne

  -- Main estimate logic
  have estimate : ‖e'  + (e_norm⁻¹ * c) • x‖ ≥ 1 - ε := by
    let c' := e_norm⁻¹ * c
    rcases le_or_gt M ‖c'‖ with h_large | h_small
    ·  -- Case 1: c' is large, c' • x dominates
      calc ‖e' + c' • x‖
        _ = ‖c' • x + e'‖                       := by rw [add_comm]
        _ ≥ ‖c' • x‖ - ‖(e' : StrongDual 𝕜 X)‖  := norm_sub_le_norm_add _ _
        _ = ‖c'‖ * ‖x‖ - 1                      := by rw [norm_smul, norm_coe, he'_norm]
        _ ≥ M * δ - 1                           := by gcongr; exact h_norm_S x hxS
        _ = (2 / δ) * δ - 1                     := rfl
        _ = 1                                   := by field_simp [hδ]; ring
        _ ≥ 1 - ε                               := by linarith
    · -- Case 2: c' is small, e dominates
      obtain this := hF_cover (mem_sphere_zero_iff_norm.mpr he'_norm)
      rw [Set.mem_iUnion₂] at this
      obtain ⟨v, hvF, hv_lower⟩ := this

      calc ‖e' + c' • x‖
        _ ≥ ‖(e' + c' • x) v‖               := ContinuousLinearMap.unit_le_opNorm _ _ v.property
        _ = ‖(e' : StrongDual 𝕜 X) v + (c' • x) v‖          := by simp only
          [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
        _ ≥ ‖(e' : StrongDual 𝕜 X) v‖ - ‖c' • x v‖          := norm_sub_le_norm_add _ _
        _ ≥ ‖(e' : StrongDual 𝕜 X) v‖ - ‖c'‖ * ‖x v‖        := by rw [norm_smul]
        _ ≥ (1 - ε / 2) - M * γ          := by
            have : ‖x v‖ < γ := hwW v (Finset.mem_coe.mp hvF)
            gcongr
            exact hv_lower.le
        _ = 1 - ε                        := by dsimp [M, γ]; field_simp [hδ.ne']; ring

  -- Reconstruct for original e and c
  calc ‖(e : StrongDual 𝕜 X) + c • x‖
    _ = ‖(e_norm : 𝕜) • (e' : StrongDual 𝕜 X) + ((e_norm : 𝕜) * ((e_norm⁻¹ : 𝕜) * c)) • x‖ := by
      -- Substitute e = e_norm • e'
      -- Substitute c = e_norm * (e_norm⁻¹ * c)
      simp only [e', e_norm]
      sorry
    _ = ‖(e_norm : 𝕜) • ((e' : StrongDual 𝕜 X) + ((e_norm⁻¹ : 𝕜) * c) • x)‖ := by
      rw [smul_add, smul_smul]
    _ = ‖(e_norm : 𝕜)‖ * ‖(e' : StrongDual 𝕜 X) + ((e_norm⁻¹ : 𝕜) * c) • x‖ := by
      rw [norm_smul]
    _ = ‖e‖ * ‖(e' : StrongDual 𝕜 X) + ((e_norm⁻¹ : 𝕜) * c) • x‖ := by
      -- 4. Simplify norm of the real scalar e_norm
      sorry
      -- rw [norm_algebraMap']
      -- dsimp only [Real.norm_eq_abs, AddSubgroupClass.coe_norm]
      -- rw [abs_of_nonneg (norm_nonneg e)]
      -- rw [norm_coe]
    _ ≥ ‖e‖ * (1 - ε) := by
      -- 5. Apply the normalized estimate
      gcongr
      exact estimate
    _ = (1 - ε) * ‖e‖ := mul_comm _ _




/-- Given a set in the dual that is bounded away from 0 in norm but has 0 in its
    weak-star closure, we can select a basic sequence with basis constant close to 1. -/
theorem basic_sequence_selection_dual {S : Set (StrongDual 𝕜 X)}
    (h_weak_star : (0 : StrongDual 𝕜 X) ∈ closure (StrongDual.toWeakDual '' S))
    (h_norm : (0 : StrongDual 𝕜 X) ∉ closure S)
    {ε : ℝ} (hε : ε > 0) :
    ∃ (f : ℕ → StrongDual 𝕜 X) (hf : IsBasicSequence 𝕜 f), (∀ n, f n ∈ S) ∧
    basicSequenceConstant hf < 1 + ε := by
  sorry

/-- In an infinite-dimensional normed space, we can find basic sequences
    with basis constant arbitrarily close to 1. -/
theorem exists_basic_sequence (hinf : ¬ FiniteDimensional 𝕜 X) {ε : ℝ} (hε : 0 < ε) :
    ∃ (x : ℕ → X) (hx : IsBasicSequence 𝕜 x), basicSequenceConstant hx < 1 + ε := by
  sorry

/-- Perturbing a basic sequence by an element outside its closed span
    yields another basic sequence. -/
lemma perturb_basic_sequence {e : ℕ → X} (he : IsBasicSequence 𝕜 e) (f : StrongDual 𝕜 X)
    (hf : ∀ n, f (e n) = 0) (u : X) (hu : u ∉ (span 𝕜 (range e)).topologicalClosure) :
    IsBasicSequence 𝕜 (fun n ↦ e n + u) := by
    sorry

/-- There are no basic sequences in a subset `S` of `X` if and only if
    the weak-star closure of the `S` is weakly-compact and does not contain `0`. -/
theorem no_basic_sequence_iff_zero_not_in_weak_star_closure {S : Set X} :
    (∀ (e : ℕ → X), ¬ IsBasicSequence 𝕜 e) ↔ (0 : X) ∉ closure ((toWeakSpace 𝕜 X )'' S) := by
  sorry

end BasicSequences
