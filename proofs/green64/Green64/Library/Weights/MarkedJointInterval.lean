module

public import Green64.Library.Weights.Part086
public import Green64.Library.Weights.Part042
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas

@[expose] public section

/-!
# Weights / MarkedJointInterval

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalMarkedJointInterval -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- A signed-shift simultaneous divisibility class exists exactly when the
true overlap divides the shift. The complete lcm, not a coprime surrogate,
is retained. This is a local ingredient of the original marked count below. -/
private theorem B543_joint_class434 (M N : ℕ) (h : ℤ)
    (hh : (M.gcd N : ℤ) ∣ h) :
    ∃ r : ℤ, ∀ w : ℤ,
      ((M:ℤ) ∣ w ∧ (N:ℤ) ∣ w+h) ↔
      Int.ModEq (M.lcm N : ℤ) w r := by
  obtain ⟨c,rfl⟩ := hh
  let r : ℤ := -(M:ℤ)*Nat.gcdA M N*c
  have hM : (M:ℤ) ∣ r := ⟨-Nat.gcdA M N*c, by dsimp [r]; ring⟩
  have hN : (N:ℤ) ∣ r+(M.gcd N:ℤ)*c := by
    refine ⟨Nat.gcdB M N*c,?_⟩
    rw [Nat.gcd_eq_gcd_ab]
    dsimp [r]
    ring
  refine ⟨r,fun w => ?_⟩
  rw [Int.modEq_iff_dvd]
  have hlcm : (M.lcm N:ℤ) ∣ r-w ↔
      (M:ℤ) ∣ r-w ∧ (N:ℤ) ∣ r-w := by
    simpa only [Int.lcm_natCast_natCast] using
      (Int.coe_lcm_dvd_iff (a := (M:ℤ)) (b := (N:ℤ)) (c := r-w))
  rw [hlcm]
  constructor
  · rintro ⟨hwM,hwN⟩
    exact ⟨dvd_sub hM hwM,by simpa using dvd_sub hN hwN⟩
  · rintro ⟨hwM,hwN⟩
    refine ⟨?_,?_⟩
    · simpa using dvd_sub hM hwM
    · convert dvd_sub hN hwN using 1; ring

/-- The exact integer interval count has endpoint discrepancy at most one
residue, with no asymptotic or smoothing hypothesis. -/
private theorem B543_residue_interval_error434
    (q : ℕ) (hq : 0 < q) (A B r : ℤ) (hAB : A ≤ B) :
    |(q:ℝ)*(((Finset.Ioc A B).filter
      (fun w => Int.ModEq (q:ℤ) w r)).card:ℝ) - ((B-A:ℤ):ℝ)| ≤ q := by
  have hqI : (0:ℤ) < q := by exact_mod_cast hq
  have hcard := Int.Ioc_filter_modEq_card A B hqI r
  simp only [←Int.cast_sub,Int.cast_natCast,Rat.floor_intCast_div_natCast] at hcard
  have hdiv : (A-r)/(q:ℤ) ≤ (B-r)/(q:ℤ) :=
    Int.ediv_le_ediv hqI (by omega)
  rw [max_eq_left (sub_nonneg.mpr hdiv)] at hcard
  have hA0 := Int.emod_nonneg (A-r) (ne_of_gt hqI)
  have hB0 := Int.emod_nonneg (B-r) (ne_of_gt hqI)
  have hAq := Int.emod_lt_of_pos (A-r) hqI
  have hBq := Int.emod_lt_of_pos (B-r) hqI
  have hAd := Int.mul_ediv_add_emod (A-r) (q:ℤ)
  have hBd := Int.mul_ediv_add_emod (B-r) (q:ℤ)
  have heq : (q:ℤ)*(((Finset.Ioc A B).filter
      (fun w => Int.ModEq (q:ℤ) w r)).card:ℤ) - (B-A) =
      (A-r)%(q:ℤ)-(B-r)%(q:ℤ) := by
    rw [hcard]
    nlinarith
  have herr : |(q:ℤ)*(((Finset.Ioc A B).filter
      (fun w => Int.ModEq (q:ℤ) w r)).card:ℤ) - (B-A)| ≤ (q:ℤ) := by
    rw [heq]
    exact abs_le.mpr ⟨by omega,by omega⟩
  exact_mod_cast herr

private theorem B543_joint_interval_error434
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (A B h : ℤ) (hAB : A ≤ B) :
    |((M*N:ℕ):ℝ)*(((Finset.Ioc A B).filter
      (fun w => (M:ℤ) ∣ w ∧ (N:ℤ) ∣ w+h)).card:ℝ) -
      ((B-A:ℤ):ℝ)*(if (M.gcd N:ℤ) ∣ h then (M.gcd N:ℝ) else 0)| ≤
      ((M*N:ℕ):ℝ) := by
  by_cases hc : (M.gcd N:ℤ) ∣ h
  · obtain ⟨r,hr⟩ := B543_joint_class434 M N h hc
    have heq : ((Finset.Ioc A B).filter
        (fun w => (M:ℤ) ∣ w ∧ (N:ℤ) ∣ w+h)) =
        ((Finset.Ioc A B).filter (fun w => Int.ModEq (M.lcm N:ℤ) w r)) := by
      ext w
      simp only [Finset.mem_filter,hr]
    rw [heq,ite_eq_left hc]
    have hp := B543_residue_interval_error434
      (M.lcm N) (Nat.lcm_pos hM hN) A B r hAB
    have hg : (M.gcd N:ℝ)*(M.lcm N:ℝ)=((M*N:ℕ):ℝ) := by
      exact_mod_cast Nat.gcd_mul_lcm M N
    have hident (c : ℝ) : ((M*N:ℕ):ℝ)*c-((B-A:ℤ):ℝ)*(M.gcd N:ℝ) =
        (M.gcd N:ℝ)*((M.lcm N:ℝ)*c-((B-A:ℤ):ℝ)) := by
      rw [←hg]
      ring
    rw [hident,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    exact (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)).trans_eq hg
  · have heq : ((Finset.Ioc A B).filter
        (fun w => (M:ℤ) ∣ w ∧ (N:ℤ) ∣ w+h)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw hdiv
      have hgM : (M.gcd N:ℤ) ∣ (M:ℤ) := by exact_mod_cast Nat.gcd_dvd_left M N
      have hgN : (M.gcd N:ℤ) ∣ (N:ℤ) := by exact_mod_cast Nat.gcd_dvd_right M N
      exact hc (by simpa using dvd_sub (hgN.trans hdiv.2) (hgM.trans hdiv.1))
    simp only [heq,Finset.card_empty,Nat.cast_zero,mul_zero,ite_eq_right hc,sub_zero,abs_zero]
    positivity


section Original
variable {ι G : Type} [Fintype ι] [DecidableEq ι]
  [Fintype G] [DecidableEq G]
variable {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
variable (d : SourceComparisonData434 ι G cfg x L Y Hprime)
  (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
local notation "X" => SourceOriginalVariableBIGState434
  (fun g : G => {p : ℕ // p ∈ d.Tb g})
  (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)

/-- The natural product of the literal labelled original free BIG marks.
Repeated independent-state coordinates remain present; original physical
injectivity is imposed in the marked-list count, not silently forgotten. -/
noncomputable def sourceOriginalB543FreePrimeNatProduct434 (a : X) : ℕ :=
  ∏ g : G, ∏ i : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g),
    (a g i).val

theorem source_original_B543_prime_product_positive434 (a : X) :
    0 < sourceOriginalB543FreePrimeNatProduct434 d J ell m hmJ ν a := by
  apply Finset.prod_pos
  intro g hg
  apply Finset.prod_pos
  intro i hi
  exact (d.hTbPrime g (a g i).val (a g i).property).pos

theorem source_original_B543_prime_product_real434 (a : X) :
    (sourceOriginalB543FreePrimeNatProduct434 d J ell m hmJ ν a : ℝ) =
      sourceOriginalB542FreePrimeProduct434 d J ell m hmJ ν a := by
  unfold sourceOriginalB543FreePrimeNatProduct434 sourceOriginalB542FreePrimeProduct434
  push_cast
  rfl

/-- Exact original ordered, injective mark mask. Under the original
disjoint-group hypothesis, the complete marked product divides the
physical position if and only if its numeric list belongs to bigMarkLists. -/
theorem source_original_B543_original_mark_mask_product434
    (hDisj : ∀ g h p,p ∈ d.Tb g → p ∈ d.Tb h → g=h)
    (a : X) (ha : ∀ g,Function.Injective (fun i => (a g i).val)) (n : ℕ) :
    (fun g i => (a g i).val) ∈
      bigMarkLists d.Tb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) n ↔
      sourceOriginalB543FreePrimeNatProduct434 d J ell m hmJ ν a ∣ n := by
  let f : (Σ g : G,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g)) → ℕ :=
    fun z => (a z.1 z.2).val
  have hf : Function.Injective f := by
    rintro ⟨g,i⟩ ⟨h,j⟩ he
    have hgh : g=h := hDisj g h (a g i).val (a g i).property
      (by have hev : (a g i).val = (a h j).val := he
          rw [hev]
          exact (a h j).property)
    subst h
    have hij : i=j := ha g he
    subst j
    rfl
  have hco : Set.Pairwise (Finset.univ : Finset
      (Σ g : G,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g)))
      (Nat.Coprime.onFun f) := by
    intro i hi j hj hij
    exact (Nat.coprime_primes
      (d.hTbPrime i.1 _ (a i.1 i.2).property)
      (d.hTbPrime j.1 _ (a j.1 j.2).property)).mpr (fun he => hij (hf he))
  have hprod : sourceOriginalB543FreePrimeNatProduct434 d J ell m hmJ ν a ∣ n ↔
      ∀ g i,(a g i).val ∣ n := by
    unfold sourceOriginalB543FreePrimeNatProduct434
    rw [←Fintype.prod_sigma f,←Finset.lcm_eq_prod hco,Finset.lcm_dvd_iff]
    simp only [Finset.mem_univ,true_implies,Sigma.forall,f]
  rw [hprod]
  simp only [bigMarkLists,Fintype.mem_piFinset,orderedBigMarks,Finset.mem_filter]
  constructor
  · intro h g i
    exact (Finset.mem_filter.mp ((h g).1 i)).2
  · intro h g
    refine ⟨(fun i => ?_),ha g⟩
    exact Finset.mem_filter.mpr ⟨(a g i).property,h g i⟩

/-- Count of the original two physical marked-list masks in a signed
integer interval. The target is literally w+k_C D_C; its positivity is
proved before converting to Nat. No sourceCore or cofactor weight is
claimed to be constant or smooth in this count. -/
noncomputable def sourceOriginalB543MarkedJointIntervalCount434
    (a b : X) (A B kC : ℤ) (DC : ℕ) : ℕ :=
  ((Finset.Ioc A B).filter (fun w =>
    (fun g i => (a g i).val) ∈
      bigMarkLists d.Tb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) w.toNat ∧
    (fun g i => (b g i).val) ∈
      bigMarkLists d.Tb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
        (w+kC*(DC:ℤ)).toNat)).card

/-- Quantitative normalized simultaneous-divisibility sampling for the
literal original distinct BIG-prime marks, with exact gcd overlap and
all original dependent free-slot counts. The bound is uniform in the
signed physical shift and can be specialized to k_C=2*k_T. -/
theorem source_original_B543_original_marked_joint_interval_error434
    (hDisj : ∀ g h p,p ∈ d.Tb g → p ∈ d.Tb h → g=h)
    (a b : X)
    (ha : ∀ g,Function.Injective (fun i => (a g i).val))
    (hb : ∀ g,Function.Injective (fun i => (b g i).val))
    (A B kC : ℤ) (DC : ℕ) (hAB : A < B)
    (hA : 0 ≤ A) (hShift : 0 ≤ A+kC*(DC:ℤ)) :
    let Ma := sourceOriginalB543FreePrimeNatProduct434 d J ell m hmJ ν a
    let Mb := sourceOriginalB543FreePrimeNatProduct434 d J ell m hmJ ν b
    |(((Ma*Mb:ℕ):ℝ) / ((B-A:ℤ):ℝ))*
        (sourceOriginalB543MarkedJointIntervalCount434 d J ell m hmJ ν a b A B kC DC:ℝ) -
      (if (Ma.gcd Mb:ℤ) ∣ kC*(DC:ℤ) then (Ma.gcd Mb:ℝ) else 0)| ≤
      ((Ma*Mb:ℕ):ℝ) / ((B-A:ℤ):ℝ) := by
  dsimp only
  let Ma := sourceOriginalB543FreePrimeNatProduct434 d J ell m hmJ ν a
  let Mb := sourceOriginalB543FreePrimeNatProduct434 d J ell m hmJ ν b
  have heq : sourceOriginalB543MarkedJointIntervalCount434
      d J ell m hmJ ν a b A B kC DC =
      ((Finset.Ioc A B).filter
        (fun w => (Ma:ℤ) ∣ w ∧ (Mb:ℤ) ∣ w+kC*(DC:ℤ))).card := by
    unfold sourceOriginalB543MarkedJointIntervalCount434
    congr 1
    apply Finset.filter_congr
    intro w hw
    have hw0 : 0 ≤ w := by have := (Finset.mem_Ioc.mp hw).1; omega
    have hwp0 : 0 ≤ w+kC*(DC:ℤ) := by
      have := (Finset.mem_Ioc.mp hw).1
      omega
    rw [source_original_B543_original_mark_mask_product434 d J ell m hmJ ν hDisj a ha,
      source_original_B543_original_mark_mask_product434 d J ell m hmJ ν hDisj b hb]
    dsimp only [Ma,Mb]
    rw [←Int.natCast_dvd_natCast,←Int.natCast_dvd_natCast,
      Int.toNat_of_nonneg hw0,Int.toNat_of_nonneg hwp0]
  rw [heq]
  have hbound := B543_joint_interval_error434 Ma Mb
    (source_original_B543_prime_product_positive434 d J ell m hmJ ν a)
    (source_original_B543_prime_product_positive434 d J ell m hmJ ν b)
    A B (kC*(DC:ℤ)) hAB.le
  have hH : (0:ℝ) < ((B-A:ℤ):ℝ) := by exact_mod_cast sub_pos.mpr hAB
  have hid (P C T : ℝ) : (P / ((B-A:ℤ):ℝ))*C-T =
      (P*C-((B-A:ℤ):ℝ)*T)/((B-A:ℤ):ℝ) := by
    field_simp [ne_of_gt hH]
  rw [hid,abs_div,abs_of_pos hH]
  exact (div_le_div_iff_of_pos_right hH).mpr hbound

end Original
end Green64Analytic.CorrelationSquare

end

end

