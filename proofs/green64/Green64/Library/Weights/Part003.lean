module

public import Green64.Library.Weights.Part002
public import Mathlib

@[expose] public section

/-!
# Weights / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ChronologicalBirthListEquiv -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.CorrelationSquare

set_option autoImplicit false

/-- Literal marked-row source carrier: retain the ordered birth list, its
numerical Nodup proof, and disjointness from all previously seen values. -/
abbrev SourceChronologicalSeenBirthList434 (ι : Type) [DecidableEq ι] :=
  {p : Finset ι × List ι // p.2.Nodup ∧ Disjoint p.1 p.2.toFinset}

/-- The corresponding target carrier.  The complete birth list is retained,
and its numerical values are contained in the updated seen set. -/
abbrev TargetChronologicalSeenBirthList434 (ι : Type) [DecidableEq ι] :=
  {p : Finset ι × List ι // p.2.Nodup ∧ p.2.toFinset ⊆ p.1}

/-- Exact list-retaining chronological equivalence used by the literal CLEAN
gate `births.Nodup ∧ Disjoint S births.toFinset`. -/
def sourceChronologicalSeenBirthListEquiv434
    (ι : Type) [DecidableEq ι] :
    SourceChronologicalSeenBirthList434 ι ≃
      TargetChronologicalSeenBirthList434 ι where
  toFun p := ⟨(p.1.1 ∪ p.1.2.toFinset, p.1.2), ⟨p.2.1, by
    intro x hx
    exact Finset.mem_union_right _ hx⟩⟩
  invFun q := ⟨(q.1.1 \ q.1.2.toFinset, q.1.2), ⟨q.2.1, by
    rw [Finset.disjoint_left]
    intro x hxDiff hxBirth
    exact (Finset.mem_sdiff.mp hxDiff).2 hxBirth⟩⟩
  left_inv p := by
    rcases p with ⟨⟨S, births⟩, hNodup, hDisjoint⟩
    apply Subtype.ext
    apply Prod.ext
    · ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxS | hxB, hnotB⟩
        · exact hxS
        · exact (hnotB hxB).elim
      · intro hxS
        exact ⟨Or.inl hxS, fun hxB =>
          (Finset.disjoint_left.mp hDisjoint hxS hxB).elim⟩
    · rfl
  right_inv q := by
    rcases q with ⟨⟨T, births⟩, hNodup, hSubset⟩
    apply Subtype.ext
    apply Prod.ext
    · ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (⟨hxT, _⟩ | hxB)
        · exact hxT
        · exact hSubset hxB
      · intro hxT
        by_cases hxB : x ∈ births.toFinset
        · exact Or.inr hxB
        · exact Or.inl ⟨hxT, hxB⟩
    · rfl

/-- The exact updated state appearing in
`sourceOriginalMarkedCleanIndexedTerm434`. -/
theorem source_chronological_birth_list_target434
    (ι : Type) [DecidableEq ι]
    (p : SourceChronologicalSeenBirthList434 ι) :
    (sourceChronologicalSeenBirthListEquiv434 ι p).1.1 =
      p.1.1 ∪ p.1.2.toFinset := by
  rfl

/-- Exact weighted pushforward while retaining the complete ordered list. -/
theorem source_chronological_birth_list_finset_pushforward434
    (ι M : Type) [DecidableEq ι] [AddCommMonoid M]
    (A : Finset (SourceChronologicalSeenBirthList434 ι))
    (W : TargetChronologicalSeenBirthList434 ι → M) :
    (A.map (sourceChronologicalSeenBirthListEquiv434 ι).toEmbedding).sum W =
      A.sum (fun p => W (sourceChronologicalSeenBirthListEquiv434 ι p)) := by
  simpa using
    (Finset.sum_map (sourceChronologicalSeenBirthListEquiv434 ι).toEmbedding A W)

/-- Literal future evaluation after the list-retaining pushforward. -/
theorem source_chronological_birth_list_future434
    (Out ι : Type) [DecidableEq ι]
    (F : Out → Finset ι → ℂ) (Y : Out)
    (p : SourceChronologicalSeenBirthList434 ι) :
    F Y (sourceChronologicalSeenBirthListEquiv434 ι p).1.1 =
      F Y (p.1.1 ∪ p.1.2.toFinset) := by
  rfl

/-- Exact weighted L² transport for the literal list-retaining carrier.  The
source weight is pulled to the target by the inverse equivalence, so this
applies directly to harmonic AUX, OLD/Fock and orbit masses without replacing
them by counting measure. -/
theorem source_chronological_birth_list_weighted_L2_pushforward434
    (ι : Type) [DecidableEq ι]
    (A : Finset (SourceChronologicalSeenBirthList434 ι))
    (w : SourceChronologicalSeenBirthList434 ι → ℝ)
    (F : TargetChronologicalSeenBirthList434 ι → ℂ) :
    (A.map (sourceChronologicalSeenBirthListEquiv434 ι).toEmbedding).sum
      (fun q => w ((sourceChronologicalSeenBirthListEquiv434 ι).symm q) * ‖F q‖ ^ 2) =
      A.sum (fun p =>
        w p * ‖F (sourceChronologicalSeenBirthListEquiv434 ι p)‖ ^ 2) := by
  simpa using
    (Finset.sum_map (sourceChronologicalSeenBirthListEquiv434 ι).toEmbedding A
      (fun q =>
        w ((sourceChronologicalSeenBirthListEquiv434 ι).symm q) * ‖F q‖ ^ 2))

end Green64Analytic.CorrelationSquare

end

end

/-! ## WeightedComplexCauchy -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 6000000

/-- Exact weighted complex Cauchy-Schwarz for any REAL SIGNED
coefficients. It charges the total absolute mass, NOT the number
of sparse cells. This is usable directly for the original signed
D20 Delta and sharp zero-extended Knu complementary-divisor mask. -/
theorem green64_finite_signed_complex_L2_Cauchy434
    {ι : Type} (S : Finset ι)
    (D : ι → ℝ) (F : ι → ℂ) :
    ‖∑ i ∈ S, (D i:ℂ)*F i‖^2 ≤
      (∑ i ∈ S, |D i|)*
      (∑ i ∈ S, |D i| *‖F i‖^2) := by
  classical
  let w : ι → ℝ := fun i => |D i|
  let t : ι → ℝ := fun i => ‖F i‖
  have hw (i : ι) : 0 ≤ w i := abs_nonneg _
  have ht (i : ι) : 0 ≤ t i := norm_nonneg _
  have hBound : ‖∑ i ∈ S, (D i:ℂ)*F i‖ ≤
      ∑ i ∈ S, w i*t i := by
    calc
      _ ≤ ∑ i ∈ S, ‖(D i:ℂ)*F i‖ := norm_sum_le _ _
      _ = ∑ i ∈ S, w i*t i := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [w,t]
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have hNormSq : ‖∑ i ∈ S, (D i:ℂ)*F i‖^2 ≤
      (∑ i ∈ S,w i*t i)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hBound 2
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i)*t i)
  have hSqrtWeight :
      (∑ i ∈ S, Real.sqrt (w i)*
        (Real.sqrt (w i)*t i)) =
      ∑ i ∈ S, w i*t i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc,Real.mul_self_sqrt (hw i)]
  have hSqrtMass :
      (∑ i ∈ S, (Real.sqrt (w i))^2) =
      ∑ i ∈ S, w i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (hw i)
  have hSqrtEnergy :
      (∑ i ∈ S, (Real.sqrt (w i)*t i)^2) =
      ∑ i ∈ S, w i*(t i)^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow,Real.sq_sqrt (hw i)]
  rw [hSqrtWeight,hSqrtMass,hSqrtEnergy] at hCS
  dsimp only [w,t] at hCS ⊢
  exact hNormSq.trans hCS
end Green64FullPhysicalE

end

end

/-! ## ActualRealProfiles -/

section

open MeasureTheory
open scoped FourierTransform BigOperators Classical
namespace Green64Analytic.ShiftTwoTerminal

/-- Fixed before the splitting precision K0, exactly as in source05. -/
noncomputable def sourceAllocationBuffer (r : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 4 * (r+1 : ℝ)
  rOut := 4 * (r+1 : ℝ) + 1
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

noncomputable def sourceBufferedGateReal (r : ℕ) (d : Bool) (t : ℝ) : ℝ :=
  sourceAllocationBuffer r t *
    (if d then Real.smoothTransition t else 1 - Real.smoothTransition t)

theorem source_buffered_gate_smooth (r : ℕ) (d : Bool) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t => (sourceBufferedGateReal r d t : ℂ)) := by
  have hb : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t => sourceBufferedGateReal r d t) := by
    cases d
    · exact (sourceAllocationBuffer r).contDiff.mul
        (contDiff_const.sub Real.smoothTransition.contDiff)
    · exact (sourceAllocationBuffer r).contDiff.mul Real.smoothTransition.contDiff
  exact Complex.ofRealCLM.contDiff.comp hb

theorem source_buffered_gate_compact (r : ℕ) (d : Bool) :
    HasCompactSupport (fun t => (sourceBufferedGateReal r d t : ℂ)) := by
  have hb : HasCompactSupport (sourceBufferedGateReal r d) :=
    (sourceAllocationBuffer r).hasCompactSupport.mul_right
  exact hb.comp_left (g := fun x : ℝ => (x : ℂ)) (by rfl)

noncomputable def sourceBufferedGate (r : ℕ) (d : Bool) : SchwartzMap ℝ ℂ :=
  (source_buffered_gate_compact r d).toSchwartzMap (source_buffered_gate_smooth r d)

@[simp] theorem source_buffered_gate_apply (r : ℕ) (d : Bool) (t : ℝ) :
    sourceBufferedGate r d t = (sourceBufferedGateReal r d t : ℂ) := rfl

theorem source_buffered_gate_bounds (r : ℕ) (d : Bool) (t : ℝ) :
    0 ≤ sourceBufferedGateReal r d t ∧ sourceBufferedGateReal r d t ≤ 1 := by
  have hρ₀ := (sourceAllocationBuffer r).nonneg (x := t)
  have hρ₁ := (sourceAllocationBuffer r).le_one (x := t)
  have hγ₀ := Real.smoothTransition.nonneg t
  have hγ₁ := Real.smoothTransition.le_one t
  cases d <;> simp only [sourceBufferedGateReal, Bool.false_eq_true,
    ↓reduceIte] <;> constructor <;> nlinarith

theorem source_buffered_gate_partition (r : ℕ) (t : ℝ) :
    sourceBufferedGateReal r false t + sourceBufferedGateReal r true t =
      sourceAllocationBuffer r t := by
  simp only [sourceBufferedGateReal, Bool.false_eq_true, ↓reduceIte]
  ring

theorem source_buffered_gate_agrees (r : ℕ) (d : Bool) (t : ℝ)
    (ht : |t| ≤ 4*(r+1 : ℝ)) :
    sourceBufferedGateReal r d t =
      if d then Real.smoothTransition t else 1 - Real.smoothTransition t := by
  have hρ : sourceAllocationBuffer r t = 1 := by
    apply (sourceAllocationBuffer r).one_of_mem_closedBall
    simpa [Metric.mem_closedBall, Real.dist_eq, sourceAllocationBuffer] using ht
  simp only [sourceBufferedGateReal, hρ, one_mul]


/-- The source's fixed smooth cutoff, with its genuine support assumption. -/
noncomputable def sourceLogCutoffFun (Psi : ℝ → ℝ) (t : ℝ) : ℂ :=
  (Psi (Real.exp t) : ℂ)

theorem source_log_cutoff_compact (Psi : ℝ → ℝ)
    (hs : Function.support Psi ⊆ Set.Icc 1 2) :
    HasCompactSupport (sourceLogCutoffFun Psi) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (0:ℝ) (Real.log 2)) isCompact_Icc
  intro t ht
  have hn : Psi (Real.exp t) ≠ 0 := by
    simpa [Function.mem_support,sourceLogCutoffFun] using ht
  have h := hs hn
  constructor
  · have hh : Real.exp 0 ≤ Real.exp t := by simpa using h.1
    exact Real.exp_le_exp.mp hh
  · have hh : Real.exp t ≤ Real.exp (Real.log 2) := by
      rw [Real.exp_log (by norm_num : (0:ℝ) < 2)]
      exact h.2
    exact Real.exp_le_exp.mp hh

theorem source_log_cutoff_smooth (Psi : ℝ → ℝ)
    (hPsi : ContDiff ℝ (↑(⊤ : ℕ∞)) Psi) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (sourceLogCutoffFun Psi) :=
  Complex.ofRealCLM.contDiff.comp (hPsi.comp Real.contDiff_exp)

noncomputable def sourceLogCutoff (Psi : ℝ → ℝ)
    (hPsi : ContDiff ℝ (↑(⊤ : ℕ∞)) Psi)
    (hs : Function.support Psi ⊆ Set.Icc 1 2) : SchwartzMap ℝ ℂ :=
  (source_log_cutoff_compact Psi hs).toSchwartzMap (source_log_cutoff_smooth Psi hPsi)


end Green64Analytic.ShiftTwoTerminal

end

/-! ## UnitFactorProgression -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceDivisorMoment
set_option autoImplicit false
set_option maxHeartbeats 6000000

def b593UnitFactorProgression (Y b q a : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 (Y/b)).filter (fun x=>Nat.ModEq q (b*x) a)

/-- Once the complementary product b is a unit, the remaining factor
occupies one actual residue class. The +1 lattice error is retained. -/
theorem b593_unit_factor_progression_card434
    (Y b q a : ℕ) (hunit : q.Coprime b) :
    (b593UnitFactorProgression Y b q a).card ≤ Y/(b*q)+1 := by
  let S := b593UnitFactorProgression Y b q a
  have hm : Set.MapsTo (fun x:ℕ=>x/q) (↑S)
      (↑(Finset.range ((Y/b)/q+1))) := by
    intro x hx
    have hxY : x≤Y/b := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hx).1).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hxY))
  have hinj : Set.InjOn (fun x:ℕ=>x/q) (↑S) := by
    intro x hx y hy heq
    have hxy : Nat.ModEq q (b*x) (b*y) :=
      (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    have hmod : Nat.ModEq q x y := hxy.cancel_left_of_coprime hunit
    change x%q=y%q at hmod
    change x/q=y/q at heq
    calc
      x=x%q+q*(x/q) := (Nat.mod_add_div x q).symm
      _=y%q+q*(y/q) := by rw [hmod,heq]
      _=y := Nat.mod_add_div y q
  have hh := Finset.card_le_card_of_injOn (fun x:ℕ=>x/q) hm hinj
  simpa only [Finset.card_range,Nat.div_div_eq_div_mul] using hh

/-- Real form of the same exact progression density, with its full
lattice error. No estimate for a divisor moment is assumed. -/
theorem b593_unit_factor_progression_real434
    (Y b q a : ℕ) (hb : 0<b) (hq : 0<q) (hunit : q.Coprime b) :
    ((b593UnitFactorProgression Y b q a).card:ℝ) ≤
      (Y:ℝ)/((b:ℝ)*(q:ℝ))+1 := by
  have hd : 0<(b:ℝ)*(q:ℝ) := by positivity
  have hdiv : ((Y/(b*q):ℕ):ℝ) ≤ (Y:ℝ)/((b:ℝ)*(q:ℝ)) := by
    apply (le_div_iff₀ hd).mpr
    exact_mod_cast Nat.div_mul_le_self Y (b*q)
  have hcard : ((b593UnitFactorProgression Y b q a).card:ℝ) ≤
      ((Y/(b*q):ℕ):ℝ)+1 := by
    exact_mod_cast b593_unit_factor_progression_card434 Y b q a hunit
  linarith

/-- A largest coordinate gives the exact hyperbola complementary-product
bound b^(r+1) ≤ n^r. This is valid for repeated factors and all integers. -/
theorem b593_largest_removed_product434
    (r : ℕ) (x : Fin (r+1) → ℕ) (j : Fin (r+1))
    (hmax : ∀i,x i≤x j) :
    (∏ i:Fin r,x (j.succAbove i))^(r+1) ≤ (∏i,x i)^r := by
  let b := ∏i:Fin r,x (j.succAbove i)
  have hb : b≤(x j)^r := by
    calc
      b ≤ ∏ _i:Fin r,x j := by
        apply Finset.prod_le_prod
        intro i hi
        exact hmax (j.succAbove i)
      _ = (x j)^r := by simp
  calc
    _ = b^r*b := by rw [pow_succ]
    _ ≤ b^r*(x j)^r := Nat.mul_le_mul_left _ hb
    _ = (x j*b)^r := by rw [mul_pow];exact Nat.mul_comm _ _
    _ = _ := by rw [Fin.prod_univ_succAbove x j]

/-- The specific sixteen-factor hyperbola range required for tau^4. -/
theorem b593_d16_largest_complement434
    (Y : ℕ) (x : Fin 16 → ℕ) (j : Fin 16)
    (hmax : ∀i,x i≤x j) (hprod : (∏i,x i)≤Y) :
    (∏i:Fin 15,x (j.succAbove i))^16 ≤ Y^15 :=
  (b593_largest_removed_product434 15 x j hmax).trans
    (Nat.pow_le_pow_left hprod 15)

/-- The original unit residue forces BOTH the selected largest factor
and its entire complementary product to be units of the same modulus. -/
theorem b593_unit_residue_complement434
    (r q a : ℕ) (x : Fin (r+1)→ℕ) (j : Fin (r+1))
    (ha : q.Coprime a) (hres : Nat.ModEq q (∏i,x i) a) :
    q.Coprime (x j) ∧ q.Coprime (∏i:Fin r,x (j.succAbove i)) := by
  have hu : q.Coprime (∏i,x i) := by
    change Nat.gcd q (∏i,x i)=1
    change (∏i,x i)%q=a%q at hres
    rw [Nat.gcd_rec q (∏i,x i),hres,←Nat.gcd_rec q a]
    exact ha
  rw [Fin.prod_univ_succAbove x j] at hu
  exact Nat.coprime_mul_iff_right.mp hu
end Green64Analytic.SourceDivisorMoment

end

end

/-! ## FiniteHyperbola -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceDivisorMoment
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Positive complementary tuples with their actual product cutoff. -/
def b593HyperbolaPrefixes (r B : ℕ) : Finset (Fin r→ℕ) :=
  (Fintype.piFinset (fun _ : Fin r=>Finset.Ioc 0 B)).filter
    (fun p=>(∏i,p i)≤B)

/-- Finite largest-factor hyperbola decomposition in a UNIT progression.
The density and the complete +1 lattice term are proved from the actual
remaining-factor congruence. The cutoff premise is a pure power inequality,
not a divisor-moment estimate. -/
theorem b593_finite_unit_hyperbola434
    (r Y B q a : ℕ) (S : Finset (Fin (r+1)→ℕ))
    (ha : q.Coprime a)
    (hpos : ∀x∈S,∀i,0<x i)
    (hsize : ∀x∈S,(∏i,x i)≤Y)
    (hres : ∀x∈S,Nat.ModEq q (∏i,x i) a)
    (hcut : Y^r<(B+1)^(r+1)) :
    S.card ≤ (r+1)*∑ p ∈ b593HyperbolaPrefixes r B,
      (Y/((∏i,p i)*q)+1) := by
  have hex : ∀x : Fin (r+1)→ℕ,∃j : Fin (r+1),∀i,x i≤x j := by
    intro x
    obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
    exact ⟨j,fun i=>hmax i (Finset.mem_univ i)⟩
  choose largest hlargest using hex
  let P := (b593HyperbolaPrefixes r B).filter (fun p=>q.Coprime (∏i,p i))
  let R := P.sigma (fun p=>b593UnitFactorProgression Y (∏i,p i) q a)
  let F : (Fin (r+1)→ℕ) → Fin (r+1) × (Σ _p : Fin r→ℕ,ℕ) :=
    fun x=>(largest x,⟨Fin.removeNth (largest x) x,x (largest x)⟩)
  have hmap : Set.MapsTo F (↑S) (↑((Finset.univ : Finset (Fin (r+1))) ×ˢ R)) := by
    intro x hx
    let j := largest x
    let p : Fin r→ℕ := Fin.removeNth j x
    let b := ∏i,p i
    have hpPos (i : Fin r) : 0<p i := hpos x hx (j.succAbove i)
    have hbPos : 0<b := Finset.prod_pos (fun i hi=>hpPos i)
    have hprod : x j*b=∏i,x i := (Fin.prod_univ_succAbove x j).symm
    have hbPow : b^(r+1)≤Y^r :=
      (b593_largest_removed_product434 r x j (hlargest x)).trans
        (Nat.pow_le_pow_left (hsize x hx) r)
    have hbB : b≤B := by
      by_contra hn
      have hh : B+1≤b := by omega
      have hpw := Nat.pow_le_pow_left hh (r+1)
      omega
    have hpMem : p∈b593HyperbolaPrefixes r B := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Fintype.mem_piFinset.mpr
        intro i
        refine Finset.mem_Ioc.mpr ⟨hpPos i,?_⟩
        exact (Nat.le_of_dvd hbPos (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))).trans hbB
      · exact hbB
    have hu := b593_unit_residue_complement434 r q a x j ha (hres x hx)
    have hpP : p∈P := Finset.mem_filter.mpr ⟨hpMem,hu.2⟩
    have hxR : x j∈b593UnitFactorProgression Y b q a := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Ioc.mpr
        refine ⟨hpos x hx j,?_⟩
        apply (Nat.le_div_iff_mul_le hbPos).mpr
        rw [hprod]
        exact hsize x hx
      · simpa only [←hprod,Nat.mul_comm] using hres x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_sigma.mpr ⟨hpP,hxR⟩⟩
  have hinj : Set.InjOn F (↑S) := by
    intro x hx y hy heq
    have hj : largest x=largest y := congrArg (fun z=>z.1) heq
    have hp : Fin.removeNth (largest x) x=Fin.removeNth (largest y) y :=
      congrArg (fun z=>z.2.1) heq
    have hv : x (largest x)=y (largest y) := congrArg (fun z=>z.2.2) heq
    calc
      x=Fin.insertNth (largest x) (x (largest x))
          (Fin.removeNth (largest x) x) := (Fin.insertNth_self_removeNth _ _).symm
      _=Fin.insertNth (largest y) (y (largest y))
          (Fin.removeNth (largest y) y) := by rw [hp,hv,hj]
      _=y := Fin.insertNth_self_removeNth _ _
  have hcard : S.card≤(r+1)*∑p∈P,(b593UnitFactorProgression Y (∏i,p i) q a).card := by
    have hh := Finset.card_le_card_of_injOn F hmap hinj
    simpa only [R,Finset.card_product,Finset.card_univ,Fintype.card_fin,
      Finset.card_sigma] using hh
  calc
    S.card≤(r+1)*∑p∈P,(b593UnitFactorProgression Y (∏i,p i) q a).card := hcard
    _≤(r+1)*∑p∈P,(Y/((∏i,p i)*q)+1) := by
      apply Nat.mul_le_mul_left
      apply Finset.sum_le_sum
      intro p hp
      exact b593_unit_factor_progression_card434 Y (∏i,p i) q a
        (Finset.mem_filter.mp hp).2
    _≤_ := by
      apply Nat.mul_le_mul_left
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p hp hpnot=>Nat.zero_le _)
end Green64Analytic.SourceDivisorMoment

end

end

/-! ## RealHyperbola -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceDivisorMoment
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Actual real density plus the full complementary-tuple lattice mass.
This is a proved finite hyperbola estimate, before applying harmonic sums. -/
theorem b593_finite_unit_hyperbola_real434
    (r Y B q a : ℕ) (S : Finset (Fin (r+1)→ℕ))
    (hq : 0<q) (ha : q.Coprime a)
    (hpos : ∀x∈S,∀i,0<x i)
    (hsize : ∀x∈S,(∏i,x i)≤Y)
    (hres : ∀x∈S,Nat.ModEq q (∏i,x i) a)
    (hcut : Y^r<(B+1)^(r+1)) :
    (S.card:ℝ) ≤ (r+1:ℝ)*
      ((Y:ℝ)/(q:ℝ)*
        (∑p∈b593HyperbolaPrefixes r B,1/((∏i,p i:ℕ):ℝ))+
        ((b593HyperbolaPrefixes r B).card:ℝ)) := by
  let P := b593HyperbolaPrefixes r B
  have hc : (S.card:ℝ) ≤ (r+1:ℝ)*
      ∑p∈P,(((Y/((∏i,p i)*q):ℕ):ℝ)+1) := by
    exact_mod_cast b593_finite_unit_hyperbola434 r Y B q a S ha hpos hsize hres hcut
  have hterm (p:Fin r→ℕ) (hp:p∈P) :
      ((Y/((∏i,p i)*q):ℕ):ℝ)+1 ≤
        (Y:ℝ)/(q:ℝ)*(1/((∏i,p i:ℕ):ℝ))+1 := by
    have hppos (i:Fin r) : 0<p i :=
      (Finset.mem_Ioc.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hp).1 i)).1
    have hb : 0<(∏i,p i:ℕ) := Finset.prod_pos (fun i hi=>hppos i)
    have hbr : 0<((∏i,p i:ℕ):ℝ) := by exact_mod_cast hb
    have hqr : 0<(q:ℝ) := by exact_mod_cast hq
    have hdiv : ((Y/((∏i,p i)*q):ℕ):ℝ) ≤
        (Y:ℝ)/(((∏i,p i:ℕ):ℝ)*(q:ℝ)) := by
      apply (le_div_iff₀ (mul_pos hbr hqr)).mpr
      exact_mod_cast Nat.div_mul_le_self Y ((∏i,p i)*q)
    calc
      _≤(Y:ℝ)/(((∏i,p i:ℕ):ℝ)*(q:ℝ))+1 := by linarith
      _=_ := by field_simp
  calc
    _≤(r+1:ℝ)*∑p∈P,(((Y/((∏i,p i)*q):ℕ):ℝ)+1) := hc
    _≤(r+1:ℝ)*∑p∈P,((Y:ℝ)/(q:ℝ)*(1/((∏i,p i:ℕ):ℝ))+1) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _=_ := by rw [Finset.sum_add_distrib,←Finset.mul_sum];simp [P]
end Green64Analytic.SourceDivisorMoment

end

end

