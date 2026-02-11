/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.SchauderBasis.Existence
public import Mathlib.Topology.Maps.Basic

/-!
# Eberlein–Šmulian Theorem

The Eberlein–Šmulian theorem states that in a Banach space, a weakly countably compact set
is weakly compact.

## Main Results

* `Eberlein_Smulian`: A weakly countably compact set in a Banach space is weakly compact.
-/

@[expose] public section

noncomputable section

open Submodule Set WeakDual Metric Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace BasicSequence

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

/-- From an injective function `σ : ℕ → ℕ`, extract a subsequence `ψ` such that
    both `ψ` and `σ ∘ ψ` are strictly monotone. -/
lemma exists_strictMono_comp_strictMono (σ : ℕ → ℕ) (hσ : Function.Injective σ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ StrictMono (σ ∘ ψ) := by
  -- σ injective on ℕ implies σ tends to atTop
  have hσ_tendsto : Filter.Tendsto σ Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    have hfin : Set.Finite (σ ⁻¹' Set.Iic b) :=
      (Set.finite_Iic b).preimage (hσ.injOn)
    obtain ⟨N, hN⟩ := hfin.bddAbove
    exact ⟨N + 1, fun n hn => by
      by_contra h; push_neg at h
      have hmem : n ∈ σ ⁻¹' Set.Iic b := le_of_lt h
      exact absurd (hN hmem) (by omega)⟩
  -- The predicate "σ(n) > M" holds frequently for any M, so we can extract
  -- a subsequence where σ is strictly increasing
  -- Build ψ using Nat.rec: ψ(0) = 0, ψ(n+1) = first k > ψ(n) with σ(k) > σ(ψ(n))
  have h_exists : ∀ n : ℕ, ∃ k, n < k ∧ σ n < σ k := by
    intro n
    obtain ⟨M, hM⟩ := Filter.tendsto_atTop_atTop.mp hσ_tendsto (σ n + 1)
    refine ⟨max (n + 1) M, lt_of_lt_of_le (Nat.lt_succ_of_le le_rfl) (le_max_left _ _),
      Nat.lt_of_succ_le (hM _ (le_max_right _ _))⟩
  -- Define ψ by recursion
  let next (n : ℕ) : ℕ := (h_exists n).choose
  have h_next_gt (n : ℕ) : n < next n := (h_exists n).choose_spec.1
  have h_next_σ (n : ℕ) : σ n < σ (next n) := (h_exists n).choose_spec.2
  -- ψ(k) = next^k(0)
  let ψ : ℕ → ℕ := fun k => next^[k] 0
  refine ⟨ψ, ?_, ?_⟩
  · -- StrictMono ψ
    apply strictMono_nat_of_lt_succ
    intro n
    simp only [ψ, Function.iterate_succ', Function.comp_def]
    exact h_next_gt _
  · -- StrictMono (σ ∘ ψ)
    apply strictMono_nat_of_lt_succ
    intro n
    simp only [Function.comp_def, ψ, Function.iterate_succ', Function.comp_def]
    exact h_next_σ _

open scoped Pointwise in
theorem IsCountablyCompact.isVonNBounded
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    {A : Set E} (hA : IsCountablyCompact A) :
    Bornology.IsVonNBounded 𝕜 A := by
  by_contra h_not
  rw [Bornology.IsVonNBounded] at h_not
  push_neg at h_not
  obtain ⟨V, hV, habs⟩ := h_not
  -- Get balanced W ⊆ V with W ∈ 𝓝 0
  obtain ⟨W, ⟨hW_nhds, hW_bal⟩, hWV⟩ := (nhds_basis_balanced 𝕜 E).mem_iff.mp hV
  have h_not_abs_W : ¬ Absorbs 𝕜 W A := fun h => habs (h.mono_left hWV)
  -- ∃ᶠ a in cobounded 𝕜, ¬(A ⊆ a • W)
  have h_freq := Filter.not_eventually.mp h_not_abs_W
  -- Using the basis of cobounded: for each n, ∃ a with ‖a‖ ≥ n+1 and ¬(A ⊆ a • W)
  have h_extract : ∀ n : ℕ, ∃ a : 𝕜, (↑n + 1 : ℝ) ≤ ‖a‖ ∧ ∃ x ∈ A, x ∉ a • W := by
    intro n
    have := ((Filter.hasBasis_cobounded_norm (E := 𝕜)).frequently_iff).mp h_freq (↑n + 1) trivial
    obtain ⟨a, ha_norm, ha_not⟩ := this
    exact ⟨a, ha_norm, Set.not_subset.mp ha_not⟩
  choose a ha_norm x hx_mem hx_not using h_extract
  -- a n ≠ 0 since ‖a n‖ ≥ n + 1 ≥ 1 > 0
  have ha_ne : ∀ n, a n ≠ 0 := by
    intro n hn
    have h := ha_norm n; simp [hn] at h; linarith [Nat.cast_nonneg' (α := ℝ) n]
  -- x n ∉ a n • W implies (a n)⁻¹ • x n ∉ W
  have hinv_not : ∀ n, (a n)⁻¹ • x n ∉ W := by
    intro n
    rw [← Set.mem_smul_set_iff_inv_smul_mem₀ (ha_ne n)]
    exact hx_not n
  -- Get cluster point from countable compactness
  obtain ⟨p, _, hp_cluster⟩ := hA x hx_mem
  -- By continuity of smul at (0, p): since 0 • p = 0 ∈ W
  have hcont : Filter.Tendsto (fun (cx : 𝕜 × E) => cx.1 • cx.2) (𝓝 0 ×ˢ 𝓝 p) (𝓝 0) := by
    have := (continuous_smul (M := 𝕜) (X := E)).continuousAt (x := (0, p))
    rwa [ContinuousAt, zero_smul, nhds_prod_eq] at this
  -- Get U ∈ 𝓝 (0 : 𝕜) and S ∈ 𝓝 p such that U × S maps into W under smul
  obtain ⟨U, hU_mem, S, hS_mem, hUS⟩ := Filter.mem_prod_iff.mp (hcont hW_nhds)
  -- (a n)⁻¹ → 0 since ‖a n‖ → ∞
  have h_inv_tendsto : Filter.Tendsto (fun n => (a n)⁻¹) Filter.atTop (𝓝 (0 : 𝕜)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => by rw [norm_inv]; exact inv_anti₀ (by positivity) (ha_norm n))
      (tendsto_inv_atTop_zero.comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop))
  -- Eventually (a n)⁻¹ ∈ U
  have h_ev_U : ∀ᶠ n in Filter.atTop, (a n)⁻¹ ∈ U :=
    h_inv_tendsto hU_mem
  -- Frequently x n ∈ S (since p is a cluster point)
  have h_fr_S : ∃ᶠ n in Filter.atTop, x n ∈ S :=
    hp_cluster.frequently hS_mem
  -- Combine: frequently both hold
  have h_both := h_fr_S.and_eventually h_ev_U
  -- Get a contradiction
  obtain ⟨n, hxS, haU⟩ := h_both.exists
  exact hinv_not n (hUS (Set.mk_mem_prod haU hxS))

open scoped Pointwise in
theorem IsCountablyCompact_IsBounded
    (A : Set (WeakSpace 𝕜 X))
    (hA : IsCountablyCompact A) : Bornology.IsBounded ((toWeakSpace 𝕜 X).symm '' A) := by
  rw [isBounded_iff_forall_norm_le]
  -- A is weakly von Neumann bounded
  have hVNB := hA.isVonNBounded (𝕜 := 𝕜)
  set S := (toWeakSpace 𝕜 X).symm '' A
  -- Pointwise boundedness: ∀ f in dual, (J x)(f) is bounded over x ∈ S
  have h_ptwise : ∀ f : X →L[𝕜] 𝕜, ∃ C, ∀ (i : ↥S),
      ‖(NormedSpace.inclusionInDoubleDual 𝕜 X (↑i)) f‖ ≤ C := by
    intro f
    -- The evaluation x ↦ f(x) is weakly continuous
    have hf_cont : Continuous (fun (x : WeakSpace 𝕜 X) =>
        ((topDualPairing 𝕜 X).flip x) f) :=
      WeakBilin.eval_continuous _ f
    -- Preimage of ball 0 1 is a weak neighborhood of 0
    have hV_mem : (fun (x : WeakSpace 𝕜 X) => ((topDualPairing 𝕜 X).flip x) f) ⁻¹'
        (Metric.ball 0 1) ∈ 𝓝 (0 : WeakSpace 𝕜 X) := by
      apply hf_cont.continuousAt.preimage_mem_nhds
      simp [Metric.ball_mem_nhds]
    -- VNB gives absorption
    obtain ⟨r, hr_pos, hr_abs⟩ := (hVNB hV_mem).exists_pos
    -- Find scalar c with ‖c‖ > r
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 r
    have hc_ne : c ≠ 0 := norm_pos_iff.mp (hr_pos.trans hc)
    have hsub := hr_abs c (le_of_lt hc)
    refine ⟨‖c‖, fun ⟨x, hx⟩ => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx
    -- y ∈ A ⊆ c • V, so c⁻¹ • y ∈ V
    have hy_mem := hsub hy
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc_ne] at hy_mem
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hy_mem
    -- By linearity: ‖c⁻¹‖ * ‖(topDualPairing.flip y) f‖ < 1
    simp only [map_smul, LinearMap.smul_apply, norm_smul] at hy_mem
    -- Key: (J ((toWeakSpace).symm y)) f = (topDualPairing.flip y) f (by rfl)
    change ‖((topDualPairing 𝕜 X).flip y) f‖ ≤ ‖c‖
    -- From hy_mem: ‖c⁻¹‖ * ‖...‖ < 1, deduce ‖...‖ < ‖c‖
    rw [norm_inv] at hy_mem
    have hc_pos : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc_ne
    rw [inv_mul_lt_iff₀ hc_pos] at hy_mem
    linarith
  -- Apply Banach-Steinhaus (uniform boundedness principle)
  obtain ⟨C, hC⟩ := banach_steinhaus h_ptwise
  -- From ‖J x‖ ≤ C, conclude ‖x‖ ≤ C via Hahn-Banach (norm_le_dual_bound)
  exact ⟨C, fun x hx => by
    have h := hC ⟨x, hx⟩
    exact NormedSpace.norm_le_dual_bound 𝕜 x
      (le_trans (ContinuousLinearMap.opNorm_nonneg _) h) (fun f =>
      le_trans (((NormedSpace.inclusionInDoubleDual 𝕜 X) x).le_opNorm f)
        (mul_le_mul_of_nonneg_right h (norm_nonneg f)))⟩

theorem Eberlein_Smulian' [CompleteSpace X] (A : Set (WeakSpace 𝕜 X))
    (hA : IsCountablyCompact A) : IsSeqCompact A := by
  intro xn h_mem
  -- Get a weak cluster point x ∈ A
  obtain ⟨x, hxA, hx_cluster⟩ := hA xn h_mem
  -- View the sequence in X (norm topology) vs WeakSpace 𝕜 X
  -- WeakSpace 𝕜 X is definitionally X, so we can cast freely
  let xnX : ℕ → X := xn
  let xX : X := x
  -- Case split: is x a norm cluster point?
  by_cases h_sep : ∃ ε > 0, ∀ᶠ n in atTop, ε ≤ ‖xnX n - xX‖
  · -- Case B: x is NOT a norm cluster point (tail is ε-separated)
    -- Extract ε and N for the separation
    obtain ⟨ε, hε, hev⟩ := h_sep
    obtain ⟨N, hN⟩ := hev.exists_forall_of_atTop
    -- Define the tail sequence and the shifted set S
    let xn'X : ℕ → X := fun n => xnX (n + N)
    let S : Set X := Set.range (fun n => xn'X n - xX)
    -- S is nonempty
    have hS_ne : S.Nonempty := ⟨xn'X 0 - xX, Set.mem_range_self 0⟩
    -- 0 ∉ norm closure of S (ε-separation)
    have h_norm_0 : (0 : X) ∉ closure S := by
      intro h0
      rw [Metric.mem_closure_iff] at h0
      obtain ⟨y, hy, hd⟩ := h0 ε hε
      obtain ⟨n, rfl⟩ := hy
      rw [dist_comm, dist_eq_norm, sub_zero] at hd
      exact not_lt.mpr (hN (n + N) (Nat.le_add_left N n)) hd
    -- 0 ∈ weak closure of S
    have h_weak_0 : (0 : X) ∈ closure (toWeakSpace 𝕜 X '' S) := by
      -- x is a weak cluster point of xn, hence of the tail
      have h_tail_cluster : MapClusterPt x atTop (fun n => xn (n + N)) := by
        rw [mapClusterPt_iff_frequently]
        intro s hs
        have hf := mapClusterPt_iff_frequently.mp hx_cluster s hs
        rw [Filter.frequently_atTop] at hf ⊢
        intro a; obtain ⟨n, hn, hns⟩ := hf (a + N)
        exact ⟨n - N, by omega, by rwa [show n - N + N = n from by omega]⟩
      -- So 0 is a weak cluster point of xn(· + N) - x
      have h_sub_cluster : MapClusterPt (0 : WeakSpace 𝕜 X) atTop
          (fun n => xn (n + N) - x) := by
        have : (fun n => xn (n + N) - x) = (· - x) ∘ (fun n => xn (n + N)) := rfl
        rw [this]; rw [show (0 : WeakSpace 𝕜 X) = x - x from (sub_self x).symm]
        exact h_tail_cluster.tendsto_comp
          (continuous_id.sub continuous_const).continuousAt.tendsto
      -- The range is contained in toWeakSpace '' S
      have h_range : ∀ n, (fun n => xn (n + N) - x) n ∈ toWeakSpace 𝕜 X '' S :=
        fun n => ⟨xn'X n - xX, Set.mem_range_self n, rfl⟩
      exact clusterPt_iff_forall_mem_closure.mp h_sub_cluster.clusterPt
        (toWeakSpace 𝕜 X '' S) (Filter.mem_map.mpr (Filter.Eventually.of_forall h_range))
    -- By contrapositive of not_mem_weakClosure_of_no_basicSequence: get a basic sequence in S
    obtain ⟨e, he_mem, he_basic⟩ :=
      exists_basicSequence_of_weakClosure_not_normClosure hS_ne h_norm_0 h_weak_0
    -- Each e k ∈ S gives σ(k) with e k = xn'X(σ(k)) - xX
    choose σ hσ using he_mem
    -- σ is injective (e is injective since it's a basic sequence)
    have he_inj : Function.Injective e := by
      have := he_basic.toBasicSequence.injective
      rwa [IsBasicSequence.coe_toBasicSequence] at this
    have hσ_inj : Function.Injective σ := by
      intro k₁ k₂ hk
      apply he_inj
      have h1 := hσ k₁; have h2 := hσ k₂; rw [hk] at h1; exact h1.symm.trans h2
    -- Extract ψ with StrictMono ψ and StrictMono (σ ∘ ψ)
    obtain ⟨ψ, hψ_mono, hσψ_mono⟩ := exists_strictMono_comp_strictMono σ hσ_inj
    -- Define yn = xn(σ(·) + N)
    let yn : ℕ → WeakSpace 𝕜 X := fun k => xn (σ k + N)
    -- Show any weak cluster point of yn equals x
    have h_unique : ∀ y : WeakSpace 𝕜 X, MapClusterPt y atTop yn → y = x := by
      intro y hy_cluster
      have h_fn_eq : yn = (fun k => toWeakSpace 𝕜 X (e k + xX)) := by
        ext k; exact sub_eq_iff_eq_add.mp (hσ k)
      rw [h_fn_eq] at hy_cluster
      exact weakClusterPt_of_basicSequence_add he_basic xX hy_cluster
    -- By unique cluster point argument: yn → x weakly
    have h_yn_mem : ∀ n, yn n ∈ A := fun n => h_mem (σ n + N)
    have h_yn_tendsto : Tendsto yn atTop (𝓝 x) :=
      unique_clusterPt_limit A hA x yn h_yn_mem h_unique
    -- Extract the strictly monotone subsequence
    let φ : ℕ → ℕ := fun k => σ (ψ k) + N
    have hφ_mono : StrictMono φ := fun _ _ hab => Nat.add_lt_add_right (hσψ_mono hab) N
    -- xn ∘ φ = yn ∘ ψ, which converges since yn → x
    have h_conv : Tendsto (xn ∘ φ) atTop (𝓝 x) := by
      change Tendsto (yn ∘ ψ) atTop (𝓝 x)
      exact h_yn_tendsto.comp hψ_mono.tendsto_atTop
    exact ⟨x, hxA, φ, hφ_mono, h_conv⟩
  · -- Case A: x IS a norm cluster point
    push_neg at h_sep
    -- h_sep : ∀ ε > 0, ∃ᶠ n in atTop, ‖xnX n - xX‖ < ε
    -- This means x is a norm-topology cluster point
    have h_norm_cluster : MapClusterPt xX atTop xnX := by
      rw [mapClusterPt_iff_frequently]
      intro s hs
      rw [Metric.mem_nhds_iff] at hs
      obtain ⟨ε, hε, hball⟩ := hs
      exact (h_sep ε hε).mono fun n hn => hball (Metric.mem_ball.mpr (by rwa [dist_eq_norm]))
    -- First-countable norm topology gives a convergent subsequence
    obtain ⟨ψ, hψ_mono, hψ_tendsto⟩ :=
      TopologicalSpace.FirstCountableTopology.tendsto_subseq h_norm_cluster
    -- Norm convergence implies weak convergence
    have h_weak_tendsto : Tendsto (xn ∘ ψ) atTop (𝓝 x) :=
      (toWeakSpaceCLM 𝕜 X).continuous.continuousAt.tendsto.comp hψ_tendsto
    exact ⟨x, hxA, ψ, hψ_mono, h_weak_tendsto⟩

-- TODO add consequeces eg: Freshet-Uryshon, reflexivity of weak compactness, etc.
/-- **Eberlein–Šmulian theorem**: In a Banach space, a weakly countably compact set
is weakly compact. -/
theorem Eberlein_Smulian [CompleteSpace X] (A : Set (WeakSpace 𝕜 X))
    (hA : IsCountablyCompact A) : IsCompact A := by
  -- Handle empty case
  by_cases hA_ne : A.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hA_ne]; exact isCompact_empty
  -- Step 1: A is bounded and closed
  have h_bounded := IsCountablyCompact_IsBounded A hA
  -- Underlying set in X
  let A_X : Set X := (toWeakSpace 𝕜 X).symm '' A
  have hA_X_eq : toWeakSpace 𝕜 X '' A_X = A := by
    change toWeakSpace 𝕜 X '' ((toWeakSpace 𝕜 X).symm '' A) = A
    rw [Set.image_image]; simp
  have hA_X_ne : A_X.Nonempty := hA_ne.image _
  -- Cache instances for dual/bidual
  letI : NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
  letI : NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance
  letI : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 X)) := inferInstance
  letI : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X)) := inferInstance
  letI : CompleteSpace (StrongDual 𝕜 (StrongDual 𝕜 X)) := inferInstance
  -- Bidual setup
  let J := NormedSpace.inclusionInDoubleDual 𝕜 X
  let ι := fun x : WeakSpace 𝕜 X => StrongDual.toWeakDual (J x)
  have hJ_iso : ∀ y, ‖J y‖ = ‖y‖ := fun y =>
    (NormedSpace.inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).norm_map y
  have hι_cont : Continuous ι :=
    (NormedSpace.inclusionInDoubleDual_isEmbedding_weak 𝕜 X).continuous
  -- Convert range ι to the expected form
  have h_range_eq : Set.range ι = StrongDual.toWeakDual '' (J '' Set.univ) := by
    ext φ; constructor
    · rintro ⟨x, rfl⟩; exact ⟨J x, ⟨x, trivial, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, _, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
  let S_bidual := J '' A_X
  let K := closure (StrongDual.toWeakDual '' S_bidual)
  -- S_bidual is bounded
  have h_S_bidual_bounded : Bornology.IsBounded S_bidual := by
    obtain ⟨R, hR⟩ := isBounded_iff_subset_closedBall 0 |>.mp h_bounded
    apply isBounded_iff_subset_closedBall 0 |>.mpr
    exact ⟨R, fun y hy => by
      obtain ⟨x, hxS, hx_eq⟩ := hy
      rw [mem_closedBall, dist_zero_right, ← hx_eq, hJ_iso]
      exact mem_closedBall_zero_iff.mp (hR hxS)⟩
  -- Membership transfer: x ∈ A_X ↔ toWeakSpace x ∈ A
  have h_mem_iff : ∀ x : X, x ∈ A_X ↔ toWeakSpace 𝕜 X x ∈ A := by
    intro x; constructor
    · rintro ⟨a, ha, rfl⟩; rwa [(toWeakSpace 𝕜 X).apply_symm_apply]
    · intro h; exact ⟨toWeakSpace 𝕜 X x, h, (toWeakSpace 𝕜 X).symm_apply_apply x⟩
  -- Main goal: show K ⊆ range(ι) in the expected form
  suffices hK : K ⊆ StrongDual.toWeakDual '' (J '' Set.univ) by
    have h_compact_cl := compactness_transfer_from_bidual A_X S_bidual rfl K rfl
      h_S_bidual_bounded hK
    rw [hA_X_eq] at h_compact_cl
    -- h_compact_cl : IsCompact (closure A), prove closure A ⊆ A
    suffices h_cl_sub : closure A ⊆ A by
      rwa [h_cl_sub.antisymm subset_closure] at h_compact_cl
    intro x₀ hx₀
    let x₀_X : X := (toWeakSpace 𝕜 X).symm x₀
    have hx₀_eq : toWeakSpace 𝕜 X x₀_X = x₀ := (toWeakSpace 𝕜 X).apply_symm_apply x₀
    haveI : T2Space (WeakSpace 𝕜 X) :=
      (WeakBilin.isEmbedding (B := (topDualPairing 𝕜 X).flip) (fun x y hxy => by
        by_contra hne
        obtain ⟨f, -, hf⟩ := exists_dual_vector 𝕜 (x - y) (sub_ne_zero.mpr hne)
        have h_eq : f x = f y := LinearMap.congr_fun hxy f
        rw [map_sub, h_eq, sub_self] at hf
        exact (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)) (by exact_mod_cast hf.symm))).t2Space
    by_cases h_norm_x : x₀_X ∈ closure A_X
    · -- Case 1: x₀ in norm closure of A_X → extract norm-convergent sequence
      haveI : FrechetUrysohnSpace X :=
        FirstCountableTopology.frechetUrysohnSpace
      obtain ⟨a, ha_mem, ha_lim⟩ := mem_closure_iff_seq_limit.mp h_norm_x
      have h_weak_lim : Filter.Tendsto (fun n => toWeakSpace 𝕜 X (a n)) atTop (𝓝 x₀) := by
        rw [← hx₀_eq]
        exact (toWeakSpaceCLM 𝕜 X).continuous.continuousAt.tendsto.comp ha_lim
      obtain ⟨y, hyA, hy_cp⟩ := hA _ (fun n => (h_mem_iff (a n)).mp (ha_mem n))
      exact (t2_iff_nhds.mp inferInstance (hy_cp.clusterPt.mono h_weak_lim)) ▸ hyA
    · -- Case 2: x₀ NOT in norm closure → use basic sequence argument
      let S : Set X := (· - x₀_X) '' A_X
      have hS_ne : S.Nonempty := hA_X_ne.image _
      -- 0 ∉ norm closure of S (translation of h_norm_x)
      have h_norm_0 : (0 : X) ∉ closure S := by
        have hS_eq : S = Homeomorph.addRight (-x₀_X) '' A_X := by
          ext y; simp [S, sub_eq_add_neg]
        rw [hS_eq, ← (Homeomorph.addRight (-x₀_X)).image_closure]
        rintro ⟨z, hz, hze⟩
        exact h_norm_x ((add_neg_eq_zero.mp hze) ▸ hz)
      -- 0 ∈ weak closure of S (from x₀ ∈ closure A via translation)
      have h_weak_0 : (0 : X) ∈ closure (toWeakSpace 𝕜 X '' S) := by
        -- toWeakSpace '' S = (· + (-x₀)) '' A in the weak topology
        have h_eq : toWeakSpace 𝕜 X '' S =
            (Homeomorph.addRight (-x₀) : WeakSpace 𝕜 X ≃ₜ WeakSpace 𝕜 X) '' A := by
          ext w; constructor
          · rintro ⟨_, ⟨a, haX, rfl⟩, rfl⟩
            refine ⟨toWeakSpace 𝕜 X a, (h_mem_iff a).mp haX, ?_⟩
            -- Goal: Homeomorph.addRight (-x₀) (toWeakSpace a) = toWeakSpace (a - x₀_X)
            simp [Homeomorph.addRight, sub_eq_add_neg, hx₀_eq]
          · rintro ⟨y, hyA, rfl⟩
            refine ⟨(toWeakSpace 𝕜 X).symm y - x₀_X,
              ⟨(toWeakSpace 𝕜 X).symm y, (h_mem_iff _).mpr ?_, rfl⟩, ?_⟩
            · rwa [(toWeakSpace 𝕜 X).apply_symm_apply]
            -- Goal: Homeomorph.addRight (-x₀) y = toWeakSpace (symm y - x₀_X)
            · simp [Homeomorph.addRight, sub_eq_add_neg, hx₀_eq]
        rw [h_eq, ← (Homeomorph.addRight (-x₀ : WeakSpace 𝕜 X)).image_closure]
        exact ⟨x₀, hx₀, by simp [Homeomorph.addRight]⟩
      -- Extract basic sequence
      obtain ⟨e, he_mem, he_basic⟩ :=
        exists_basicSequence_of_weakClosure_not_normClosure hS_ne h_norm_0 h_weak_0
      -- e n = σ n - x₀_X for some σ n ∈ A_X
      have he_mem' : ∀ n, ∃ a ∈ A_X, a - x₀_X = e n := fun n => he_mem n
      choose σ hσ_mem hσ_eq using he_mem'
      obtain ⟨y, hyA, hy_cp⟩ := hA (fun n => toWeakSpace 𝕜 X (σ n))
        (fun n => (h_mem_iff (σ n)).mp (hσ_mem n))
      -- σ n = e n + x₀_X, so apply weakClusterPt_of_basicSequence_add
      have h_fn_eq : (fun n => toWeakSpace 𝕜 X (σ n)) =
          (fun n => toWeakSpace 𝕜 X (e n + x₀_X)) := by
        ext n; congr 1; exact sub_eq_iff_eq_add.mp (hσ_eq n)
      rw [h_fn_eq] at hy_cp
      exact (weakClusterPt_of_basicSequence_add he_basic x₀_X hy_cp).trans hx₀_eq ▸ hyA
  -- Prove K ⊆ range(ι) by contradiction
  by_contra h_not_subset
  rw [Set.subset_def] at h_not_subset; push_neg at h_not_subset
  obtain ⟨w, hwK, hw_not_range⟩ := h_not_subset
  -- w ∉ range(ι) (reformulated)
  have hw_not_range_ι : w ∉ Set.range ι := by rwa [h_range_eq]
  let w' : StrongDual 𝕜 (StrongDual 𝕜 X) := WeakDual.toStrongDual w
  -- w' ∉ range(J)
  have hw'_not_range : w' ∉ Set.range J := by
    intro ⟨x, hx⟩; apply hw_not_range_ι
    exact ⟨x, show StrongDual.toWeakDual (J x) = w by
      rw [hx]; exact LinearEquiv.apply_symm_apply StrongDual.toWeakDual w⟩
  -- w' ≠ 0
  have hw'_ne : w' ≠ 0 := by
    intro h; apply hw'_not_range
    exact ⟨0, show J 0 = w' by rw [map_zero, h]⟩
  -- Find f ∈ X* with ‖w'(f)‖ > 1
  have ⟨f₀, hf₀⟩ : ∃ f₀ : StrongDual 𝕜 X, w' f₀ ≠ 0 := by
    by_contra h; push_neg at h
    exact hw'_ne (ContinuousLinearMap.ext fun g => h g)
  let c := w' f₀
  have hc_ne : c ≠ 0 := hf₀
  let f : StrongDual 𝕜 X := (2 * c⁻¹) • f₀
  have hf_val : w' f = 2 := by
    change w' ((2 * c⁻¹) • f₀) = 2
    rw [map_smul, smul_eq_mul, show w' f₀ = c from rfl, mul_assoc, inv_mul_cancel₀ hc_ne, mul_one]
  have hf_norm : 1 < ‖w' f‖ := by rw [hf_val, RCLike.norm_ofNat]; norm_num
  -- ι(x) applied to f equals f(x)
  have hι_eval : ∀ (x : X), (ι x : WeakDual 𝕜 (StrongDual 𝕜 X)) f = f x := fun _ => rfl
  -- w f = w' f
  have hw_eval : (w : WeakDual 𝕜 (StrongDual 𝕜 X)) f = w' f := rfl
  -- IsOpen for the separation set
  have h_sep_open : IsOpen {φ : WeakDual 𝕜 (StrongDual 𝕜 X) | 1 < ‖φ f‖} :=
    isOpen_lt continuous_const (continuous_norm.comp (WeakBilin.eval_continuous _ f))
  have hw_in_sep : w ∈ {φ : WeakDual 𝕜 (StrongDual 𝕜 X) | 1 < ‖φ f‖} := by
    change 1 < ‖w f‖; rw [hw_eval]; exact hf_norm
  -- Define A₀ = {x ∈ A_X | 1 < ‖f x‖}
  let A₀ : Set X := {x ∈ A_X | 1 < ‖f x‖}
  -- A₀ is nonempty: some element of toWeakDual '' S_bidual is in the separation set
  have hA₀_ne : A₀.Nonempty := by
    obtain ⟨z, hz_sep, hz_mem⟩ :=
      mem_closure_iff_nhds.mp hwK _ (h_sep_open.mem_nhds hw_in_sep)
    obtain ⟨_, ⟨x, hxA, rfl⟩, rfl⟩ := hz_mem
    exact ⟨x, hxA, hz_sep⟩
  -- A₀ is bounded
  have hA₀_bounded : Bornology.IsBounded A₀ := h_bounded.subset (fun _ hx => hx.1)
  -- Key: closure(toWeakSpace '' A₀) is NOT compact
  have h_not_compact : ¬ IsCompact (closure (toWeakSpace 𝕜 X '' A₀)) := by
    intro h_compact
    have hιC_compact : IsCompact (ι '' closure (toWeakSpace 𝕜 X '' A₀)) :=
      h_compact.image hι_cont
    have hιC_closed : IsClosed (ι '' closure (toWeakSpace 𝕜 X '' A₀)) :=
      hιC_compact.isClosed
    -- ι '' (toWeakSpace '' A₀) ⊆ ι '' closure(toWeakSpace '' A₀)
    have h_sub : ι '' (toWeakSpace 𝕜 X '' A₀) ⊆ ι '' closure (toWeakSpace 𝕜 X '' A₀) :=
      Set.image_mono subset_closure
    -- toWeakDual '' (J '' A₀) = ι '' (toWeakSpace '' A₀)
    have h_ι_A₀ : StrongDual.toWeakDual '' (J '' A₀) = ι '' (toWeakSpace 𝕜 X '' A₀) := by
      ext φ; constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨_, mem_image_of_mem _ hx, rfl⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    -- w ∈ closure(ι '' (toWeakSpace '' A₀))
    have hw_in_cl : w ∈ closure (ι '' (toWeakSpace 𝕜 X '' A₀)) := by
      rw [← h_ι_A₀, mem_closure_iff_nhds]; intro U hU
      obtain ⟨z, ⟨hzU, hz_sep⟩, hz_mem⟩ :=
        mem_closure_iff_nhds.mp hwK _ (Filter.inter_mem hU (h_sep_open.mem_nhds hw_in_sep))
      obtain ⟨_, ⟨x, hxA, rfl⟩, rfl⟩ := hz_mem
      exact ⟨StrongDual.toWeakDual (J x), hzU,
        J x, ⟨x, ⟨hxA, hz_sep⟩, rfl⟩, rfl⟩
    -- w ∈ ι '' closure(toWeakSpace '' A₀) (since ι(compact) is closed)
    have hw_in_ιC : w ∈ ι '' closure (toWeakSpace 𝕜 X '' A₀) :=
      closure_minimal h_sub hιC_closed hw_in_cl
    -- w ∈ range(ι), contradiction
    obtain ⟨y, _, rfl⟩ := hw_in_ιC
    exact hw_not_range_ι ⟨y, rfl⟩
  -- By contrapositive: A₀ contains a basic sequence
  have h_basic : ∃ (e : ℕ → X), (∀ n, e n ∈ A₀) ∧ IsBasicSequence 𝕜 e := by
    by_contra h_no; push_neg at h_no
    exact h_not_compact (no_basic_sequence_implies_relatively_weakly_compact hA₀_ne hA₀_bounded h_no)
  obtain ⟨e, he_mem, he_basic⟩ := h_basic
  -- e(n) ∈ A₀ ⊆ A_X, so toWeakSpace(e(n)) ∈ A
  have he_in_A : ∀ n, (toWeakSpace 𝕜 X) (e n) ∈ A :=
    fun n => (h_mem_iff (e n)).mp (he_mem n).1
  -- By countable compactness: ∃ a ∈ A, cluster point
  obtain ⟨a, _, ha_cluster⟩ := hA (fun n => (toWeakSpace 𝕜 X) (e n)) he_in_A
  -- By weakClusterPt_of_basicSequence_add (x₀ = 0): a = 0
  have ha_eq_0 : a = 0 := by
    have : MapClusterPt a atTop (fun n => toWeakSpace 𝕜 X (e n + 0)) := by simpa using ha_cluster
    exact (weakClusterPt_of_basicSequence_add he_basic 0 this).trans (map_zero _)
  -- f is weakly continuous
  have hf_cont : Continuous (fun x : WeakSpace 𝕜 X => f x) :=
    WeakBilin.eval_continuous (topDualPairing 𝕜 X).flip f
  -- f(a) is a cluster point of f ∘ e; f(a) = f(0) = 0
  have h_cluster_f : MapClusterPt (0 : 𝕜) atTop (fun n => f (e n)) := by
    have := MapClusterPt.continuousAt_comp hf_cont.continuousAt ha_cluster
    rwa [ha_eq_0, show f (0 : WeakSpace 𝕜 X) = 0 from map_zero f] at this
  -- But ‖f(e(n))‖ > 1 for all n, so ball(0,1) is never visited — contradiction
  obtain ⟨n, hn⟩ := (h_cluster_f.frequently (ball_mem_nhds 0 one_pos)).exists
  simp only [dist_zero_right] at hn
  exact absurd hn (not_lt.mpr (le_of_lt (he_mem n).2))

end BasicSequence

theorem CompleteNormedSpace.to_frechetUrysohn [CompleteSpace X] : FrechetUrysohnSpace X := sorry
