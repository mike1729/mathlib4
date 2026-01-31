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
public import Mathlib.Topology.Algebra.Module.WeakDual


/-!
# Basic Sequences in Banach Spaces
-/

noncomputable section

open Submodule Set WeakDual Metric Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A `BasicSequence` is a bundled sequence that forms a Schauder basis
    for its algebraic span, with a finite basis constant.
    TODO add a comment about closed span version -/
structure BasicSequence (𝕜 : Type*) (X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] where
  toFun : ℕ → X
  -- The basis field now just takes the types, not the sequence function
  basis : SchauderBasis 𝕜 (Submodule.span 𝕜 (Set.range toFun))
  -- We explicitly link the basis vectors to the sequence
  eq_basis : ⇑basis = Set.codRestrict toFun (Submodule.span 𝕜 (Set.range toFun))
                        (fun n ↦ Submodule.subset_span (Set.mem_range_self n))
  basisConstant_lt_top : basis.basisConstant < ⊤

-- Enable treating the BasicSequence as a function `ℕ → X`
instance : CoeFun (BasicSequence 𝕜 X) (fun _ ↦ ℕ → X) where
  coe b := b.toFun

/-- A sequence `e` is a basic sequence if there exists a `BasicSequence` structure
    whose underlying sequence is equal to `e`. -/
def IsBasicSequence (𝕜 : Type*) {X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) : Prop :=
  ∃ b : BasicSequence 𝕜 X, ⇑b = e

-- TODO check where complete space is needed
namespace BasicSequences

/-- The **Basis Constant** of a basic sequence. -/
noncomputable def basicSequenceConstant (bs : BasicSequence 𝕜 X) : ℝ :=
  bs.basis.basisConstant.toReal

/-- A sequence satisfies the **Grünblum Condition** if the norms of the projections
onto the span of its first `n` elements are uniformly bounded. -/
def SatisfiesGrunblumCondition (𝕜 : Type*) {X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) : Prop :=
  ∃ K, 1 ≤ K ∧ ∀ (n m : ℕ) (a : ℕ → 𝕜), m ≤ n →
    ‖∑ i ∈ Finset.range m, a i • e i‖ ≤ K * ‖∑ i ∈ Finset.range n, a i • e i‖

/-- The Grünblum constant for a basic sequence is max(1, basicSequenceConstant). -/
def grunblumConstant (bs : BasicSequence 𝕜 X) : ℝ := max 1 (basicSequenceConstant bs)

theorem grunblumConstant_ge_one (bs : BasicSequence 𝕜 X) : 1 ≤ grunblumConstant bs :=
  le_max_left 1 _

/-- A basic sequence implies the Grünblum inequality holds for its basis constant. -/
theorem grunblum_of_basic (bs : BasicSequence 𝕜 X) : SatisfiesGrunblumCondition 𝕜 bs := sorry

/-- The explicit Grünblum bound using `grunblumConstant`. -/
theorem grunblum_bound_of_basic (bs : BasicSequence 𝕜 X) (n m : ℕ) (a : ℕ → 𝕜) (hmn : m ≤ n) :
    ‖∑ i ∈ Finset.range m, a i • bs i‖ ≤
    grunblumConstant bs * ‖∑ i ∈ Finset.range n, a i • bs i‖ := sorry

lemma linearIndependent_of_grunblum {e : ℕ → X} (h_grunblum : SatisfiesGrunblumCondition 𝕜 e)
    (h_nz : ∀ n, e n ≠ 0) : LinearIndependent 𝕜 e := sorry

/--
**The Grünblum Criterion**:
If a sequence satisfies the Grünblum condition (bounded projections on the span),
and the elements are non-zero, then it is a Basic Sequence.
-/
theorem isBasicSequence_of_grunblum [CompleteSpace X] {e : ℕ → X}
    (h_grunblum : SatisfiesGrunblumCondition 𝕜 e)
    (h_nz : ∀ n, e n ≠ 0) : IsBasicSequence 𝕜 e := sorry

/-- A version of `isBasicSequence_of_grunblum` that also provides an explicit bound
    on the basis constant. If a sequence satisfies the Grünblum condition with constant K,
    the resulting basic sequence has basis constant at most K. -/
theorem isBasicSequence_of_grunblum_with_bound [CompleteSpace X] {e : ℕ → X} {K : ℝ}
    (hK_ge : 1 ≤ K)
    (hK_bound : ∀ (n m : ℕ) (a : ℕ → 𝕜), m ≤ n →
      ‖∑ i ∈ Finset.range m, a i • e i‖ ≤ K * ‖∑ i ∈ Finset.range n, a i • e i‖)
    (h_nz : ∀ n, e n ≠ 0) :
    ∃ (b : BasicSequence 𝕜 X), ⇑b = e ∧ basicSequenceConstant b ≤ K := sorry


theorem basic_sequence_selection_dual {S : Set (StrongDual 𝕜 X)}
    (h_weak_star : (0 : WeakDual 𝕜 X) ∈ closure (StrongDual.toWeakDual '' S))
    (h_norm : (0 : StrongDual 𝕜 X) ∉ closure S)
    {ε : ℝ} (hε : ε > 0) :
    -- We assert existence of the STRUCTURE 'b', which bundles the function and the constant
    ∃ (b : BasicSequence 𝕜 (StrongDual 𝕜 X)),
      (∀ n, b n ∈ S) ∧
      basicSequenceConstant b < 1 + ε := sorry

lemma perturb_basic_sequence [CompleteSpace X] (b : BasicSequence 𝕜 X) (u : X)
    (f : StrongDual 𝕜 X) (hf : ∀ n, f (b n) = 1) (hu0 : f u = 0) :
    IsBasicSequence 𝕜 (fun n ↦ b n + u) := sorry

/-- If a bounded set S in a Banach space X does not contain a basic sequence,
    then 0 is not in the weak closure of S.

    This is a consequence of the basic sequence selection principle: if 0 is in the
    weak* closure of J(S) but not in its norm closure, then J(S) contains a basic sequence,
    which can be pulled back to a basic sequence in S. -/
theorem no_basic_sequence_implies_zero_not_in_weak_closure [CompleteSpace X]
    {S : Set X} (_hS_ne : S.Nonempty) (h_norm : (0 : X) ∉ closure S)
    (h_no_basic : ∀ (e : ℕ → X), (∀ n, e n ∈ S) → ¬ IsBasicSequence 𝕜 e) :
    (0 : X) ∉ closure (toWeakSpace 𝕜 X '' S) := by
  -- We prove the contrapositive: if 0 is in the weak closure, we can find a basic sequence.
  contrapose! h_no_basic

  -- 1. Setup the Bidual embedding J : X → X**
  let J := NormedSpace.inclusionInDoubleDual 𝕜 X
  let S' := J '' S

  -- 2. Translate the weak closure hypothesis to the bidual's weak* topology.
  -- The weak topology on X and the weak* topology on X** are both induced by X*.
  -- A basic weak* neighborhood of 0 in X** is determined by finitely many f ∈ X*.
  -- The preimage under J of such a neighborhood equals the corresponding weak neighborhood
  -- of 0 in X.
  have h_weak_star : (0 : WeakDual 𝕜 (StrongDual 𝕜 X)) ∈ closure (StrongDual.toWeakDual '' S') := by
    rw [_root_.mem_closure_iff]
    intro U hU_open hU_zero
    -- U is open in weak* topology, which is induced from StrongDual 𝕜 X → 𝕜
    rw [isOpen_induced_iff] at hU_open
    obtain ⟨V, hV_open, hV_eq⟩ := hU_open
    have h0V : (fun f => (0 : WeakDual 𝕜 (StrongDual 𝕜 X)) f) ∈ V := by
      rw [← hV_eq] at hU_zero; exact hU_zero
    -- V is open in product topology, so contains a basic open set
    rw [isOpen_pi_iff] at hV_open
    obtain ⟨F, t, ht_cond, hFt_sub⟩ := hV_open _ h0V
    -- F is finite set of functionals in X*, t gives open neighborhoods in 𝕜
    -- Construct corresponding weak neighborhood W of 0 in X
    -- In WeakSpace 𝕜 X, evaluation at f ∈ X* is continuous (WeakBilin.eval_continuous)
    let W : Set (WeakSpace 𝕜 X) := ⋂ f ∈ F, {w : WeakSpace 𝕜 X | f ((toWeakSpace 𝕜 X).symm w) ∈ t f}
    have hW_open : IsOpen W := by
      apply isOpen_biInter_finset
      intro f _
      -- The evaluation map w ↦ f(w) is continuous in the weak topology
      have hf_cont : Continuous (fun w : WeakSpace 𝕜 X => f ((toWeakSpace 𝕜 X).symm w)) :=
        WeakBilin.eval_continuous (topDualPairing 𝕜 X).flip f
      exact (ht_cond f ‹f ∈ F›).1.preimage hf_cont
    have hW_zero : toWeakSpace 𝕜 X 0 ∈ W := by
      simp only [W, mem_iInter, mem_setOf, map_zero]
      intro f hf
      exact (ht_cond f hf).2
    -- Since 0 ∈ weak closure of S, W ∩ (toWeakSpace '' S) is nonempty
    have h_inter : (W ∩ (toWeakSpace 𝕜 X '' S)).Nonempty := by
      have h_cl := @_root_.mem_closure_iff (WeakSpace 𝕜 X) _
        (toWeakSpace 𝕜 X 0) (toWeakSpace 𝕜 X '' S)
      exact h_cl.mp h_no_basic W hW_open hW_zero
    obtain ⟨w, hwW, x, hxS, hwx⟩ := h_inter
    -- x ∈ S satisfies: f(x) ∈ t f for all f ∈ F
    have hx_in_t : ∀ f ∈ F, f x ∈ t f := fun f hf => by
      have := hwW
      simp only [W, mem_iInter] at this
      specialize this f hf
      simp only [mem_setOf, hwx.symm, LinearEquiv.symm_apply_apply] at this
      exact this
    -- Therefore J(x) ∈ U
    have hJx_U : StrongDual.toWeakDual (J x) ∈ U := by
      rw [← hV_eq]
      apply hFt_sub
      intro f hf
      change topDualPairing 𝕜 (StrongDual 𝕜 X) (StrongDual.toWeakDual (J x)) f ∈ t f
      simp only [topDualPairing_apply, StrongDual.coe_toWeakDual, J, NormedSpace.dual_def]
      exact hx_in_t f hf
    -- And J(x) ∈ toWeakDual '' S'
    have hJx_S' : StrongDual.toWeakDual (J x) ∈ StrongDual.toWeakDual '' S' :=
      ⟨J x, ⟨x, hxS, rfl⟩, rfl⟩
    exact ⟨StrongDual.toWeakDual (J x), hJx_U, hJx_S'⟩

  -- 3. Show 0 is not in the norm closure of S' in the bidual.
  -- Since J is an isometry, it preserves distances to the origin.
  have h_norm_S' : (0 : StrongDual 𝕜 (StrongDual 𝕜 X)) ∉ closure S' := by
    rw [Metric.mem_closure_iff]
    push_neg
    -- 0 ∉ closure S means there exists δ > 0 such that S ∩ ball(0, δ) = ∅
    rw [Metric.mem_closure_iff] at h_norm
    push_neg at h_norm
    obtain ⟨δ, hδ_pos, hδ_S⟩ := h_norm
    use δ, hδ_pos
    rintro _ ⟨x, hxS, rfl⟩
    -- J is an isometry: dist(J x, 0) = dist(x, 0)
    have hJ_iso : ‖J x‖ = ‖x‖ := (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map x
    rw [dist_zero_left, hJ_iso, ← dist_zero_left]
    exact hδ_S x hxS

  -- 4. Apply the Selection Principle for Dual Spaces with ε = 1.
  obtain ⟨b_bidual, hb_mem, -⟩ := basic_sequence_selection_dual h_weak_star h_norm_S' zero_lt_one

  -- 5. Pull the sequence back to X.
  -- Since b_bidual n ∈ S' = J '' S, there exists x_n ∈ S such that J x_n = b_bidual n.
  choose e he_S he_eq using hb_mem

  -- 6. Show e is a basic sequence in S using the Grünblum condition.
  use e, he_S

  -- e has nonzero elements (since b_bidual is basic and J is injective)
  have h_nz : ∀ n, e n ≠ 0 := fun n h_zero => by
    -- b_bidual.basis is linearly independent, so its elements are nonzero
    have hb_indep := b_bidual.basis.linearIndependent
    have hb_nz := hb_indep.ne_zero n
    -- b_bidual.eq_basis says: b_bidual.basis n = codRestrict b_bidual.toFun ... n
    -- So (b_bidual.basis n : X**) = b_bidual n
    have h_eq : (b_bidual.basis n : StrongDual 𝕜 (StrongDual 𝕜 X)) = b_bidual n := by
      have := congrFun b_bidual.eq_basis n
      exact congrArg Subtype.val this
    -- If e n = 0, then J(e n) = 0 = b_bidual n, but b_bidual n ≠ 0
    rw [← he_eq n, h_zero, map_zero] at h_eq
    -- h_eq : (b_bidual.basis n : X**) = 0, so b_bidual.basis n = 0 as subtype element
    exact hb_nz (Subtype.ext h_eq)

  -- The Grünblum constant for b_bidual
  let K := grunblumConstant b_bidual
  have hK_ge : 1 ≤ K := grunblumConstant_ge_one b_bidual

  -- Transfer Grünblum condition from b_bidual to e using J being an isometry
  have hK_bound_e : ∀ (n m : ℕ) (a : ℕ → 𝕜), m ≤ n →
      ‖∑ i ∈ Finset.range m, a i • e i‖ ≤ K * ‖∑ i ∈ Finset.range n, a i • e i‖ := by
    intro n m a hmn
    have h_J_sum (k : ℕ) : J (∑ i ∈ Finset.range k, a i • e i) =
        ∑ i ∈ Finset.range k, a i • b_bidual i := by
      simp only [map_sum, map_smul, he_eq]
    have hJ_norm : ∀ y : X, ‖J y‖ = ‖y‖ :=
      (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map
    calc ‖∑ i ∈ Finset.range m, a i • e i‖
      _ = ‖J (∑ i ∈ Finset.range m, a i • e i)‖ := (hJ_norm _).symm
      _ = ‖∑ i ∈ Finset.range m, a i • b_bidual i‖ := by rw [h_J_sum]
      _ ≤ K * ‖∑ i ∈ Finset.range n, a i • b_bidual i‖ := grunblum_bound_of_basic b_bidual n m a hmn
      _ = K * ‖J (∑ i ∈ Finset.range n, a i • e i)‖ := by rw [h_J_sum]
      _ = K * ‖∑ i ∈ Finset.range n, a i • e i‖ := by rw [hJ_norm]

  -- Apply Grünblum criterion
  exact isBasicSequence_of_grunblum ⟨K, hK_ge, hK_bound_e⟩ h_nz


def SchauderBasis_of_closure [CompleteSpace X] {Y : Submodule 𝕜 X} (b : SchauderBasis 𝕜 Y)
    (h_bound : b.basisConstant < ⊤) : SchauderBasis 𝕜 Y.topologicalClosure := by
  -- Let Z be the closure of Y. It is a Banach space.
  let Z := Y.topologicalClosure
  haveI : CompleteSpace Z := Submodule.topologicalClosure.completeSpace Y
  let inc : Y →L[𝕜] Z := (Submodule.inclusion Y.le_topologicalClosure).mkContinuous 1 (fun y => by
    simp only [one_mul, Submodule.coe_norm, Submodule.coe_inclusion, le_refl])


  have h_isometry : Isometry inc := fun y₁ y₂ => by
    simp only [inc, edist_dist, dist_eq_norm]
    congr 1

  -- inc has dense range (Y is dense in its topological closure)
  have h_dense : DenseRange inc := by
    rw [DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro z
    rw [mem_closure_iff_nhds]
    intro U hU
    -- U is a neighborhood of z in Z, find y : Y with inc y ∈ U
    rw [_root_.mem_nhds_iff] at hU
    obtain ⟨V, hVU, hVopen, hzV⟩ := hU
    -- V is open in Z, so V = W ∩ Z for some open W in X
    rw [isOpen_induced_iff] at hVopen
    obtain ⟨W, hWopen, rfl⟩ := hVopen
    -- z ∈ W and z ∈ closure Y (since z ∈ Z)
    have hz_closure : (z : X) ∈ closure (Y : Set X) := z.2
    rw [mem_closure_iff_nhds] at hz_closure
    have hW_nhd : W ∈ 𝓝  (z : X) := hWopen.mem_nhds hzV
    obtain ⟨x, hxW, hxY⟩ := hz_closure W hW_nhd
    exact ⟨inc ⟨x, hxY⟩, hVU hxW, ⟨x, hxY⟩, rfl⟩

  have h_unif : IsUniformInducing inc := h_isometry.isUniformInducing

  let P' : ℕ → Z →L[𝕜] Z := fun n ↦ (inc ∘L b.proj n).extend inc

  -- 2. Define the basis vectors in Z.
  let b' : ℕ → Z := fun n ↦ ⟨b n, Y.le_topologicalClosure (b n).2⟩

  -- Helper: P' agrees with b.proj on Y
  have h_agree (n : ℕ) (y : Y) : P' n (inc y) = inc (b.proj n y) := by
    simp only [P']
    rw [ContinuousLinearMap.extend_eq (e := inc) (inc ∘L b.proj n) h_dense h_unif y]
    rfl

  let C := b.basisConstant.toReal
  have hC : 0 ≤ C := sorry

  have h_uniform : ∀ n, ‖P' n‖ ≤ C := by
    intro n
    simp only [P']
    have h_norm : ∀ x, ‖x‖ = ‖inc x‖ := fun x ↦ h_isometry.norm_map_of_map_zero (map_zero _) x
    refine (ContinuousLinearMap.opNorm_extend_le (inc.comp (b.proj n)) (N := 1) h_dense ?_).trans ?_
    · intro x; simp only [h_norm]
      simp only [AddSubgroupClass.coe_norm, NNReal.coe_one, one_mul]
      exact le_refl _
    rw [NNReal.coe_one, one_mul]

    calc
      ‖inc.comp (b.proj n)‖ ≤ ‖inc‖ * ‖b.proj n‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖b.proj n‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        refine inc.opNorm_le_bound zero_le_one (fun x ↦ ?_)
        simp only [h_isometry.norm_map_of_map_zero (map_zero _), one_mul, le_refl]
      _ = ‖b.proj n‖ := by rw [one_mul]
      _ ≤ C := by
        dsimp only [C]
        apply (ENNReal.ofReal_le_iff_le_toReal h_bound.ne).mp
        simp only [ofReal_norm]
        exact b.norm_proj_le_basisConstant n
  have h0 : P' 0 = 0 := by
        simp only [P']
        -- b.proj 0 = 0, so inc ∘L b.proj 0 = 0, and extend of 0 is 0
        have h_proj0 : b.proj 0 = 0 := by ext x; simp [proj_apply, Finset.range_zero]
        simp only [h_proj0, ContinuousLinearMap.comp_zero,
          ContinuousLinearMap.extend_zero h_dense h_unif]
  have hdim : ∀ n, Module.finrank 𝕜 (LinearMap.range (P' n).toLinearMap) = n := by
        intro n
        -- The range of P' n equals the span of {e' 0, ..., e' (n-1)}
        have h_range_eq : LinearMap.range (P' n).toLinearMap =
            Submodule.span 𝕜 (Set.range (fun i : Fin n => banach_steinhaus' i)) := by
          apply le_antisymm
          · -- Range P' n ⊆ span {e' i | i < n}
            intro z hz
            obtain ⟨w, rfl⟩ := hz
            -- The span is finite-dimensional, hence closed
            let S := Submodule.span 𝕜 (Set.range (fun i : Fin n => b' i))
            haveI : FiniteDimensional 𝕜 S := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
            have hS_closed : IsClosed (S : Set Z) := Submodule.closed_of_finiteDimensional S
            -- Use density: if property holds on inc(Y) and is closed, it holds on Z
            have h_P'_in_S : ∀ z : Z, (P' n) z ∈ S := fun z =>
              h_dense.induction_on (p := fun z => (P' n) z ∈ S) z
                (hS_closed.preimage (P' n).continuous)
                (fun y => by
                  simp only [SetLike.mem_coe, S]
                  rw [h_agree, b.proj_apply]
                  simp_rw [map_sum, map_smul]
                  apply Submodule.sum_mem
                  intro i hi
                  have hi' : i < n := Finset.mem_range.mp hi
                  have h_b'_mem : b' i ∈ Set.range (fun j : Fin n => b' j) :=
                    ⟨⟨i, hi'⟩, rfl⟩
                  exact Submodule.smul_mem _ _ (Submodule.subset_span h_b'_mem))
            exact h_P'_in_S w
          · -- span {e' i | i < n} ⊆ range(P' n)
            rw [Submodule.span_le]
            rintro _ ⟨i, rfl⟩
            refine ⟨b' i, ?_⟩
            -- P' n (e' i) = e' i for i < n, using h_agree and proj_basis_element
            -- Key: e' k = inc (e k) by definition
            show (P' n) (b' i) = b' i
            calc (P' n) (b' i) = (P' n) (inc (b i)) := rfl
              _ = inc (b.proj n (b i)) := h_agree n (b i)
              _ = inc (b i) := by rw [b.proj_basis_element, if_pos i.is_lt]
              _ = b' i := rfl
        rw [h_range_eq, finrank_span_eq_card]
        · exact Fintype.card_fin n
        · -- Linear independence of e' restricted to Fin n
          -- e' is injective image of e under the injective map inc
          have h_inc_inj : Function.Injective inc := h_isometry.injective
          have h_ind : LinearIndependent 𝕜 b' :=
            b.linearIndependent.map' (Submodule.inclusion Y.le_topologicalClosure) (by
              simp only [Submodule.ker_inclusion])
          exact h_ind.comp (fun (i : Fin n) => (i : ℕ)) Fin.val_injective
  have hcomp : ∀ n m, ∀ x : Z, P' n (P' m x) = P' (min n m) x := by
        intro n m z
        -- Use density: prove for inc y, then extend by continuity
        apply h_dense.induction_on (p := fun z => (P' n) ((P' m) z) = (P' (min n m)) z) z
        · -- The set {z | P' n (P' m z) = P' (min n m) z} is closed
          exact isClosed_eq ((P' n).continuous.comp (P' m).continuous) (P' (min n m)).continuous
        · -- For y : Y, P' n (P' m (inc y)) = P' (min n m) (inc y)
          intro y
          calc (P' n) ((P' m) (inc y))
              = (P' n) (inc (b.proj m y)) := by rw [h_agree]
            _ = inc (b.proj n (b.proj m y)) := by rw [h_agree]
            _ = inc (b.proj (min n m) y) := by rw [b.proj_comp]
            _ = (P' (min n m)) (inc y) := by rw [← h_agree]
  have hlim : ∀ x, Tendsto (fun n ↦ P' n x) atTop (𝓝 x) := by
        intro z
        -- First, show convergence on inc(Y): P' n (inc y) → inc y
        have h_tendsto_on_Y : ∀ y : Y, Tendsto (fun n => (P' n) (inc y)) atTop (𝓝 (inc y)) := by
          intro y
          have h1 : ∀ n, (P' n) (inc y) = inc (b.proj n y) := fun n => h_agree n y
          simp_rw [h1]
          exact inc.continuous.continuousAt.tendsto.comp (b.proj_tendsto_id y)
        -- Use uniform bounds and density to extend to Z
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨C, hC⟩ := h_uniform
        -- We need C' + 1 > 0 for the division. C could be negative, so use max.
        set C' := max C 0 with hC'_def
        have hC'_nonneg : C' ≥ 0 := le_max_right C 0
        have hC'1_pos : C' + 1 > 0 := by linarith
        have hC'2_pos : C' + 2 > 0 := by linarith
        have hC'_bound : ∀ n, ‖P' n‖ ≤ C' := fun n => (hC n).trans (le_max_left C 0)
        -- Choose δ = ε / (2 * (C' + 2)) so that (C' + 1) * δ < ε/2
        set δ := ε / (2 * (C' + 2)) with hδ_def
        have hδ_pos : δ > 0 := div_pos hε (by linarith)
        -- Find y : Y with z close to inc y
        have hz_closure : z ∈ closure (Set.range inc) := by
          rw [h_dense.closure_eq]; exact Set.mem_univ z
        rw [Metric.mem_closure_iff] at hz_closure
        obtain ⟨_, ⟨y, rfl⟩, hw⟩ := hz_closure δ hδ_pos
        -- Find N such that P' n (inc y) is close to inc y for n ≥ N
        have h_tendsto_y := h_tendsto_on_Y y
        rw [Metric.tendsto_atTop] at h_tendsto_y
        obtain ⟨N, hN⟩ := h_tendsto_y (ε / 2) (half_pos hε)
        use N
        intro n hn
        have h_dist_z_y : dist z (inc y) < δ := hw
        have h_dist_Pn : dist ((P' n) (inc y)) (inc y) < ε / 2 := hN n hn
        have h_norm_Pn : ‖(P' n) (z - inc y)‖ ≤ C' * dist z (inc y) := by
          calc ‖(P' n) (z - inc y)‖ ≤ ‖P' n‖ * ‖z - inc y‖ := (P' n).le_opNorm _
            _ ≤ C' * ‖z - inc y‖ := mul_le_mul_of_nonneg_right (hC'_bound n) (norm_nonneg _)
            _ = C' * dist z (inc y) := by rw [dist_eq_norm]
        -- Key: (C' + 1) * δ < ε/2 since δ = ε / (2 * (C' + 2)) and C' + 1 < C' + 2
        have h_key : (C' + 1) * δ < ε / 2 := by
          rw [hδ_def]
          have h1 : (C' + 1) / (C' + 2) < 1 := by rw [div_lt_one hC'2_pos]; linarith
          have h2 : (C' + 1) * (ε / (2 * (C' + 2))) = ε / 2 * ((C' + 1) / (C' + 2)) := by
            rw [mul_div_assoc, mul_comm (C' + 1), ← mul_div_assoc, mul_comm 2, mul_assoc]
            congr 1
            rw [div_mul_eq_mul_div, mul_comm (C' + 1)]
          rw [h2]
          calc ε / 2 * ((C' + 1) / (C' + 2))
              < ε / 2 * 1 := mul_lt_mul_of_pos_left h1 (half_pos hε)
            _ = ε / 2 := mul_one _
        -- Need: (C' + 1) * dist z (inc y) < (C' + 1) * δ
        have h_dist_lt : (C' + 1) * dist z (inc y) < (C' + 1) * δ := by
          exact mul_lt_mul_of_pos_left h_dist_z_y hC'1_pos
        calc dist ((P' n) z) z
            ≤ dist ((P' n) z) ((P' n) (inc y)) + dist ((P' n) (inc y)) (inc y) +
                dist (inc y) z := dist_triangle4 _ _ _ _
          _ = ‖(P' n) (z - inc y)‖ + dist ((P' n) (inc y)) (inc y) + dist z (inc y) := by
              simp only [dist_eq_norm, map_sub, norm_sub_rev]
          _ ≤ C' * dist z (inc y) + dist ((P' n) (inc y)) (inc y) + dist z (inc y) := by
              linarith [h_norm_Pn]
          _ = (C' + 1) * dist z (inc y) + dist ((P' n) (inc y)) (inc y) := by ring
          _ < (C' + 1) * δ + ε / 2 := by linarith [h_dist_lt]
          _ < ε / 2 + ε / 2 := by linarith
          _ = ε := add_halves ε
  have h_in_range : ∀ n, b' n ∈ LinearMap.range (SchauderBasis.Q P' n).toLinearMap :=
    sorry
  have h_ne : ∀ n, b' n ≠ 0 := by
        intro n
        simp only [b', ne_eq, Submodule.mk_eq_zero]
        exact Subtype.coe_ne_coe.mpr (b.linearIndependent.ne_zero n)

  let props : SchauderBasis.CanonicalProjectionProperties 𝕜 Z := ⟨P', b', h0, hdim, hcomp, hlim, h_in_range, h_ne⟩
  exact props.basis

/-- The basis vectors of the closure basis are simply the inclusion of the original basis vectors. -/
@[simp]
theorem SchauderBasis_of_closure_apply [CompleteSpace X] {Y : Submodule 𝕜 X}
    (b : SchauderBasis 𝕜 Y) (h_bound : b.basisConstant < ⊤) (n : ℕ) :
    (SchauderBasis_of_closure b h_bound) n = ⟨b n, Y.le_topologicalClosure (b n).2⟩ := sorry

/-- Functional equality version (as requested). -/
theorem SchauderBasis_of_closure_coe [CompleteSpace X] {Y : Submodule 𝕜 X}
    (b : SchauderBasis 𝕜 Y) (h_bound : b.basisConstant < ⊤) :
    ⇑(SchauderBasis_of_closure b h_bound) = fun n ↦ ⟨b n, Y.le_topologicalClosure (b n).2⟩ := sorry

theorem SchauderBasis_of_closure' [CompleteSpace X] {Y : Submodule 𝕜 X} (b : SchauderBasis 𝕜 Y)
    (h_bound : b.basisConstant < ⊤) : SchauderBasis.IsSchauderBasis 𝕜 Y.topologicalClosure
    (fun n ↦ ⟨b n, Y.le_topologicalClosure (b n).2⟩) := sorry

theorem no_basic_sequence_implies_relatively_weakly_compact [CompleteSpace X]
    {S : Set X} (hS_ne : S.Nonempty) (h_norm : (0 : X) ∉ closure S)
    (h_bounded : Bornology.IsBounded S)
    (h_no_basic : ∀ (e : ℕ → X), (∀ n, e n ∈ S) → ¬ IsBasicSequence 𝕜 e) :
    IsCompact (closure (toWeakSpace 𝕜 X '' S)) :=

    let Xbidual := StrongDual 𝕜 (StrongDual 𝕜 X)
    let J := NormedSpace.inclusionInDoubleDual 𝕜 X
    let S_bidual := J '' S

    have h_S_bidual_bounded : Bornology.IsBounded S_bidual := by
      rw [Metric.isBounded_iff_subset_closedBall 0] at h_bounded ⊢
      obtain ⟨R, hR⟩ := h_bounded
      use R
      intro y hy
      obtain ⟨x, hxS, rfl⟩ := hy
      have hxS_norm : x ∈ closedBall 0 R := hR hxS
      rw [Metric.mem_closedBall, dist_zero_right] at *
      have hJ_iso : ‖J x‖ = ‖x‖ := (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map x
      exact hJ_iso.le.trans hxS_norm

    let K := closure (StrongDual.toWeakDual '' S_bidual)

    have hK_subset :  K ⊆ StrongDual.toWeakDual '' (J '' (Set.univ)) := by
      by_contra h_not_subset
      rw [Set.subset_def] at h_not_subset
      push_neg at h_not_subset
      obtain ⟨w, hwK, hw_not_JX⟩ := h_not_subset

      -- Define S' in StrongDual (Xbidual) space as translation of S_bidual by -w'
      let w' : Xbidual := WeakDual.toStrongDual w
      let S' := (fun y => y - w') '' S_bidual

      have h_weak_starS' : (0 : WeakDual 𝕜 (StrongDual 𝕜 X)) ∈ closure (StrongDual.toWeakDual '' S') := by
        let A := StrongDual.toWeakDual '' S_bidual
        let T : WeakDual 𝕜 (StrongDual 𝕜 X) ≃ₜ WeakDual 𝕜 (StrongDual 𝕜 X) :=
          Homeomorph.addRight (-w)
        have h_image : StrongDual.toWeakDual '' S' = T '' A := by
          simp only [S', A, S_bidual, image_image]
          apply image_congr
          intro x _
          simp only [T, Homeomorph.coe_addRight, sub_eq_add_neg, w']
          rfl
        rw [h_image, ← Homeomorph.image_closure]
        have h_zero : (0 : WeakDual 𝕜 (StrongDual 𝕜 X)) = T w := by
          simp only [T, Homeomorph.coe_addRight, add_neg_cancel]
        rw [h_zero]
        apply mem_image_of_mem
        exact hwK

      have h_normS' : (0 : Xbidual) ∉ closure S' := by
        -- We proceed by contradiction. Assume 0 ∈ closure S'.
        intro h0

        -- S' is the translation of S_bidual by -w'.
        -- Since translation is a homeomorphism, w' must be in the closure of S_bidual.
        have hw_cl : w' ∈ closure S_bidual := by
          -- Define the homeomorphism T(z) = z - w' on Xbidual
          let T := Homeomorph.addRight (-w' : Xbidual)
          -- S' = T '' S_bidual (by definition of S')
          have h_image : S' = T '' S_bidual := by
            simp only [S', S_bidual, T, Homeomorph.coe_addRight, sub_eq_add_neg, image_image]
          rw [h_image, ← Homeomorph.image_closure] at h0
          -- 0 ∈ T '' (closure S_bidual) means T.symm 0 ∈ closure S_bidual
          obtain ⟨y, hy_mem, hy_eq⟩ := h0
          have h_y_eq_w' : y = w' := by
            have : T.symm (T y) = T.symm 0 := by rw [hy_eq]
            rw [Homeomorph.symm_apply_apply] at this
            simp only [T, Homeomorph.addRight_symm, Homeomorph.coe_addRight, zero_add] at this
            rw [neg_neg] at this
            exact this
          rw [← h_y_eq_w']
          exact hy_mem

        -- The range of J is closed in X** because X is complete and J is an isometry.
        have h_JX_closed : IsClosed (range J) :=
          (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).isometry.isClosedEmbedding.isClosed_range

        -- S_bidual is contained in range J, so its norm closure is also contained in range J.
        have h_subset : closure S_bidual ⊆ range J :=
          closure_minimal (image_subset_range J S) h_JX_closed

        -- Therefore w' ∈ range J.
        have hw_in_JX : w' ∈ range J := h_subset hw_cl

        -- This contradicts the choice of w (hw_not_JX).
        apply hw_not_JX
        -- Reformulate w' ∈ range J to match hw_not_JX
        rw [image_univ]
        obtain ⟨x, hx⟩ := hw_in_JX
        use J x
        constructor
        · exact mem_range_self x
        · -- Show toWeakDual (J x) = w.
          simp only [w'] at hx
          rw [hx]
          rfl

      have h_basicS' : ∃ e : ℕ → Xbidual, (∀ n, e n ∈ S') ∧ IsBasicSequence 𝕜 e := by
        obtain ⟨b, hb_mem, -⟩ := basic_sequence_selection_dual h_weak_starS' h_normS' zero_lt_one
        use b
        constructor
        · exact hb_mem
        · exact ⟨b, rfl⟩

      obtain ⟨e, he_S', he_basic⟩ := h_basicS'
      rcases he_basic with ⟨b, rfl⟩

      have h_w_span : ∃ N : ℕ, w' ∉ closure (Submodule.span 𝕜 (Set.range (fun n => b (n+N)))) := by
        -- 1. w is non-zero (since w ∉ J(X) and 0 ∈ J(X))
        have hw_ne : w' ≠ 0 := by
          intro h
          apply hw_not_JX
          have hw0 : w = 0 := by
            apply WeakDual.toStrongDual.injective
            rw [h, map_zero]
          rw [h, image_univ]
          simp only [StrongDual.coe_toWeakDual, image_id', mem_range]
          use 0
          simp only [map_zero]

        -- 2. Assume for contradiction that w is in the closure of *all* tail spans
        by_contra h_contra
        push_neg at h_contra

        -- 3. Get the basis structure for the closure of the span
        let Y := Submodule.span 𝕜 (Set.range b.toFun)
        let Z := Y.topologicalClosure

        -- Since h_contra holds for N=0, w is in the closure of the whole span
        have h_w'_in_Z : w' ∈ Z := by
          simpa using h_contra 0

        -- Lift w to the subspace K = closure Y
        let w'_Z : Z := ⟨w', h_w'_in_Z⟩
        have hw'_Z_ne : w'_Z ≠ 0 := fun h => hw_ne (congrArg Subtype.val h)

        -- Use the theorem to treat b as a Schauder basis for K
        -- (Assuming SchauderBasis_of_closure is available as discussed)
        let basis_Z :=
        -- let basis_K : SchauderBasis 𝕜 Y.topologicalClosure :=
          SchauderBasis_of_closure b.basis b.basisConstant_lt_top

        -- 4. Since w ≠ 0, it must have a non-zero coordinate k
        have h_exists_coord : ∃ k, basis_Z.coord k w'_Z ≠ 0 := by
          by_contra! h_all_zero
          apply hw'_Z_ne
          -- If all coords are 0, the vector is 0 by the expansion property
          -- have h_exp := basis_Z.expansion (w'_Z: Z)
          have h_zero : (fun i ↦ (basis_Z.coord i) w'_Z • basis_Z i) = fun _ ↦ 0 := by
            ext i
            simp [h_all_zero i]
          rw [h_zero] at h_exp
          exact HasSum.unique h_exp hasSum_zero

        obtain ⟨k, hk_ne⟩ := h_exists_coord

        -- 5. Use the hypothesis for N = k + 1 to derive a contradiction
        -- The contradiction is: w ∈ closure(tail) implies coord k w = 0
        specialize h_contra (k + 1)

        -- The k-th coordinate functional is continuous on K
        let coord_k := basis_K.coord k

        -- We show coord_k vanishes on the tail span
        -- The tail span is generated by b_{k+1}, b_{k+2}, ...
        let tail_span := Submodule.span 𝕜 (Set.range (fun n => b.toFun (n + (k + 1))))

        -- First show tail_span ⊆ Y
        have h_tail_in_Y : tail_span ≤ Y := by
          apply Submodule.span_mono
          intro x hx
          obtain ⟨n, rfl⟩ := hx
          exact ⟨n + (k + 1), rfl⟩

        -- First prove a simpler lemma: coord_k vanishes on basis elements with index > k
        have h_vanish_basis : ∀ j > k, basis_K.coord k (basis_K j) = 0 := by
          intro j hj
          rw [SchauderBasis_of_closure.coord_apply, SchauderBasis_of_closure_apply]
          exact b.basis.ortho k j |>.trans (Pi.single_eq_of_ne hj.ne')

        -- The coordinate functional coord_k vanishes on elements of tail_span
        have h_vanish_on_tail : ∀ v (hv : v ∈ tail_span), coord_k ⟨v, Y.le_topologicalClosure (h_tail_in_Y hv)⟩ = 0 := by
          intro v hv
          -- For v in tail_span, show coord_k applied to the lifted element is 0
          sorry

        -- 6. By continuity, coord_k w must be 0
        have h_coord_w_zero : coord_k w_K = 0 := by
          -- w is a limit of a sequence in tail_span
          rw [mem_closure_iff_seq_limit] at h_contra
          obtain ⟨u, hu_tail, hu_lim⟩ := h_contra

          -- Lift the sequence to K
          let u_K (n : ℕ) : Y.topologicalClosure :=
            ⟨u n, Y.le_topologicalClosure (h_tail_in_Y (hu_tail n))⟩

          -- Convergence in K is equivalent to convergence in Xbidual for the subtype
          have h_lim_K : Filter.Tendsto u_K Filter.atTop (nhds w_K) := by
            rw [Topology.IsEmbedding.tendsto_nhds_iff Topology.IsEmbedding.subtypeVal]
            exact hu_lim

          -- coord_k is continuous, so coord_k (lim u_n) = lim (coord_k u_n)
          have h_tendsto := ((ContinuousLinearMap.continuous coord_k).tendsto w_K).comp h_lim_K

          -- But coord_k (u_n) is constantly 0
          have h_vals : ∀ n, coord_k (u_K n) = 0 := fun n ↦ h_vanish_on_tail (u n) (hu_tail n)

          -- The sequence coord_k ∘ u_K = fun _ => 0
          have h_const : (coord_k ∘ u_K) = fun _ => 0 := by
            ext n
            exact h_vals n
          rw [h_const] at h_tendsto
          -- Now h_tendsto says: (fun _ => 0) tends to coord_k w_K
          -- So coord_k w_K must be 0
          exact tendsto_const_nhds_iff.mp h_tendsto

        -- 7. Contradiction
        exact hk_ne h_coord_w_zero


      obtain ⟨N, h_w_notin_span⟩ := h_w_span
      let e := fun n => b (n + N)

      have h_sep : ∃ f : StrongDual 𝕜 Xbidual, f w' = -1 ∧ (∀ n, f (e n) = 0) := by
        -- Use Hahn-Banach separation theorem
        -- The closed subspace M = closure(span(range e)) doesn't contain w'
        let M := closure (Submodule.span 𝕜 (Set.range e) : Set Xbidual)

        -- w' ∉ M by h_w_notin_span
        have hw'_notin_M : w' ∉ M := by
          convert h_w_notin_span using 1
          simp only [M, e]
          rfl

        -- M is a closed submodule, so by Hahn-Banach geometric form,
        -- there exists a continuous linear functional separating w' from M
        -- Specifically, ∃ f : Xbidual →L[𝕜] 𝕜 such that f w' ≠ 0 and ∀ m ∈ M, f m = 0

        -- Since M contains span(range e), we have ∀ n, e n ∈ M
        have he_in_M : ∀ n, e n ∈ M := fun n => by
          apply subset_closure
          exact Submodule.subset_span ⟨n, rfl⟩

        -- Apply RCLike.geometric_hahn_banach_point_closed to separate w' from M
        -- M is a closed convex set (closure of a submodule) and w' ∉ M
        have h_exists_f : ∃ f : StrongDual 𝕜 Xbidual, f w' ≠ 0 ∧ (∀ m ∈ M, f m = 0) := by
          -- M is closed by definition (it's a closure)
          have hM_closed : IsClosed M := isClosed_closure

          -- M is convex (closure of a convex set, and submodules are convex)
          have hM_convex : Convex ℝ M := by
            apply Convex.closure
            exact convex_span ℝ _

          -- Apply geometric Hahn-Banach
          obtain ⟨g, u, hg_w', hg_M⟩ := RCLike.geometric_hahn_banach_point_closed hM_convex hM_closed hw'_notin_M

          -- Since 0 ∈ M (as M = closure of a submodule containing 0), we have re(g 0) < u
          have h0_in_M : (0 : Xbidual) ∈ M := by
            apply subset_closure
            exact Submodule.zero_mem _
          have hg_0 : RCLike.re (g 0) < u := hg_M 0 h0_in_M
          simp only [map_zero, RCLike.zero_re'] at hg_0
          have hu_pos : 0 < u := hg_0

          -- For any m ∈ M (which is a submodule after taking closure), we have re(g m) < u
          -- Since M is closed under scaling and contains 0, this forces g m = 0
          have hg_vanish : ∀ m ∈ M, g m = 0 := by
            intro m hm
            -- For any real t and m ∈ M, we have t•m ∈ M, so re(g(t•m)) = t•re(g m) < u
            -- This holds for all t ∈ ℝ, which forces re(g m) = 0
            -- Similarly for the imaginary part
            ext
            · -- Real part
              by_contra h_re_ne
              -- If re(g m) ≠ 0, then for large enough |t|, we have t•re(g m) > u or < 0
              by_cases h_pos : 0 < RCLike.re (g m)
              · -- Take t large enough so that t•re(g m) > u
                have : ∃ t : ℝ, u < t * RCLike.re (g m) := by
                  use (u / RCLike.re (g m)) + 1
                  field_simp
                  linarith
                obtain ⟨t, ht⟩ := this
                have ht_pos : 0 < t := by
                  by_contra h_not_pos
                  push_neg at h_not_pos
                  have : t * RCLike.re (g m) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h_not_pos (le_of_lt h_pos)
                  linarith
                -- But t•m ∈ M (by closure of submodule scaling), so re(g(t•m)) < u
                have htm_in_M : (t : 𝕜) • m ∈ M := by
                  -- M = closure(span ...), and span is closed under scaling
                  rw [mem_closure_iff_seq_limit]
                  obtain ⟨seq, hseq_in, hseq_lim⟩ := mem_closure_iff_seq_limit.mp hm
                  use fun n => (t : 𝕜) • seq n
                  constructor
                  · intro n
                    exact Submodule.smul_mem _ _ (hseq_in n)
                  · exact ((continuous_const_smul (t : 𝕜)).tendsto m).comp hseq_lim
                have : RCLike.re (g ((t : 𝕜) • m)) < u := hg_M _ htm_in_M
                rw [map_smul, RCLike.smul_re, RCLike.ofReal_re] at this
                linarith
              · -- re(g m) ≤ 0, take negative t
                push_neg at h_pos
                have h_neg : RCLike.re (g m) < 0 := lt_of_le_of_ne h_pos (Ne.symm h_re_ne)
                -- Take t < 0 large enough so that t•re(g m) > u
                have : ∃ t : ℝ, u < t * RCLike.re (g m) := by
                  use -(u / RCLike.re (g m)) - 1
                  field_simp
                  have : 0 < -RCLike.re (g m) := by linarith
                  nlinarith
                obtain ⟨t, ht⟩ := this
                have htm_in_M : (t : 𝕜) • m ∈ M := by
                  rw [mem_closure_iff_seq_limit]
                  obtain ⟨seq, hseq_in, hseq_lim⟩ := mem_closure_iff_seq_limit.mp hm
                  use fun n => (t : 𝕜) • seq n
                  constructor
                  · intro n
                    exact Submodule.smul_mem _ _ (hseq_in n)
                  · exact ((continuous_const_smul (t : 𝕜)).tendsto m).comp hseq_lim
                have : RCLike.re (g ((t : 𝕜) • m)) < u := hg_M _ htm_in_M
                rw [map_smul, RCLike.smul_re, RCLike.ofReal_re] at this
                linarith
            · -- Imaginary part: similar argument using I•m
              by_contra h_im_ne
              -- Scale by I to relate imaginary to real part
              have hIm_in_M : (RCLike.I : 𝕜) • m ∈ M := by
                rw [mem_closure_iff_seq_limit]
                obtain ⟨seq, hseq_in, hseq_lim⟩ := mem_closure_iff_seq_limit.mp hm
                use fun n => RCLike.I • seq n
                constructor
                · intro n
                  exact Submodule.smul_mem _ _ (hseq_in n)
                · exact ((continuous_const_smul RCLike.I).tendsto m).comp hseq_lim
              have : RCLike.re (g (RCLike.I • m)) < u := hg_M _ hIm_in_M
              rw [map_smul] at this
              -- re(I • g m) = -im(g m)
              have : RCLike.re (RCLike.I * g m) = -RCLike.im (g m) := by
                rw [RCLike.mul_re, RCLike.I_re, RCLike.I_im]
                ring
              rw [this] at this
              -- So -im(g m) < u
              -- Now use scaling by real t on I•m to force im(g m) = 0
              by_cases h_im_pos : 0 < RCLike.im (g m)
              · -- Take t < 0 such that -t•im(g m) > u
                have : ∃ t : ℝ, u < -t * RCLike.im (g m) := by
                  use -(u / RCLike.im (g m)) - 1
                  field_simp
                  nlinarith
                obtain ⟨t, ht⟩ := this
                have htIm_in_M : (t : 𝕜) • RCLike.I • m ∈ M := by
                  rw [mem_closure_iff_seq_limit]
                  obtain ⟨seq, hseq_in, hseq_lim⟩ := mem_closure_iff_seq_limit.mp hm
                  use fun n => (t : 𝕜) • RCLike.I • seq n
                  constructor
                  · intro n
                    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hseq_in n))
                  · exact ((continuous_const_smul ((t : 𝕜) • RCLike.I)).tendsto m).comp hseq_lim
                have : RCLike.re (g ((t : 𝕜) • RCLike.I • m)) < u := hg_M _ htIm_in_M
                rw [map_smul, map_smul] at this
                have : RCLike.re ((t : 𝕜) • RCLike.I * g m) = -t * RCLike.im (g m) := by
                  rw [RCLike.smul_re, RCLike.mul_re, RCLike.I_re, RCLike.I_im, RCLike.ofReal_re]
                  ring
                rw [this] at this
                linarith
              · push_neg at h_im_pos
                by_cases h_im_neg : RCLike.im (g m) < 0
                · -- Similar case with positive t
                  have : ∃ t : ℝ, u < -t * RCLike.im (g m) := by
                    use (u / (-RCLike.im (g m))) + 1
                    field_simp
                    nlinarith
                  obtain ⟨t, ht⟩ := this
                  have ht_pos : 0 < t := by
                    by_contra h_not_pos
                    push_neg at h_not_pos
                    have : 0 < -RCLike.im (g m) := by linarith
                    have : -t * RCLike.im (g m) ≤ 0 := by nlinarith
                    linarith
                  have htIm_in_M : (t : 𝕜) • RCLike.I • m ∈ M := by
                    rw [mem_closure_iff_seq_limit]
                    obtain ⟨seq, hseq_in, hseq_lim⟩ := mem_closure_iff_seq_limit.mp hm
                    use fun n => (t : 𝕜) • RCLike.I • seq n
                    constructor
                    · intro n
                      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hseq_in n))
                    · exact ((continuous_const_smul ((t : 𝕜) • RCLike.I)).tendsto m).comp hseq_lim
                  have : RCLike.re (g ((t : 𝕜) • RCLike.I • m)) < u := hg_M _ htIm_in_M
                  rw [map_smul, map_smul] at this
                  have : RCLike.re ((t : 𝕜) • RCLike.I * g m) = -t * RCLike.im (g m) := by
                    rw [RCLike.smul_re, RCLike.mul_re, RCLike.I_re, RCLike.I_im, RCLike.ofReal_re]
                    ring
                  rw [this] at this
                  linarith
                · push_neg at h_im_neg
                  -- im(g m) = 0
                  linarith

          use g
          constructor
          · -- g w' ≠ 0 because re(g w') > u > 0
            intro h
            rw [h, RCLike.zero_re'] at hg_w'
            linarith
          · exact hg_vanish

        obtain ⟨f₀, hf₀_ne, hf₀_M⟩ := h_exists_f

        -- Scale f₀ so that f₀ w' = -1
        let f := (-1 / f₀ w') • f₀

        use f
        constructor
        · -- Show f w' = -1
          simp only [f, ContinuousLinearMap.smul_apply]
          field_simp [hf₀_ne]
          ring
        · -- Show ∀ n, f (e n) = 0
          intro n
          simp only [f, ContinuousLinearMap.smul_apply]
          rw [hf₀_M (e n) (he_in_M n)]
          simp

      obtain ⟨f, hf_w, hf_e⟩ := h_sep
      have hf_sep_val: ∀ n, f ((e n) - w') = 1 := by
        intro n
        rw [map_sub, hf_e, hf_w]
        ring

      have h_basicS: IsBasicSequence 𝕜 (fun n => (e n) - w') := by
        -- use perturb_basic_sequence e w' f hf_e hf_w
        sorry

      have h_in_S : ∀ n, (e n) - w' ∈ S_bidual := by sorry

      --transfer back the basic sequence to S and get a contradiction with h_no_basic
      sorry

    -- transfer compactness back to X via weak-weak* correspondence
    sorry


end BasicSequences
