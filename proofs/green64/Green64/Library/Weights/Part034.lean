module

public import Green64.Library.Weights.DivisorPowerMajorant
public import Green64.Library.Weights.Part003
public import Green64.Library.Weights.PositiveFactorTuples

@[expose] public section

/-!
# Weights / Part034

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## IntegerHyperbolaCutoff -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceDivisorMoment
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The unit-AP size condition provides an integer hyperbola cutoff.
No real root, asymptotic cap or new analytic premise is introduced. -/
theorem b593_quotient_hyperbola_cutoff434
    (r Y q : ℕ) (hq : 0<q) (hsize : q^(r+1)≤Y) :
    Y^r<(Y/q+1)^(r+1) := by
  have hY : 0<Y := (pow_pos hq _).trans_le hsize
  have hdivision : Y<q*(Y/q+1) := by
    have hm := Nat.mod_lt Y hq
    have he := Nat.mod_add_div Y q
    nlinarith
  have hpower : Y^(r+1)<(q*(Y/q+1))^(r+1) := by gcongr
  have hcancel : Y*Y^r<Y*(Y/q+1)^(r+1) := by
    calc
      _=Y^(r+1) := by rw [pow_succ];exact Nat.mul_comm _ _
      _<(q*(Y/q+1))^(r+1) := hpower
      _=q^(r+1)*(Y/q+1)^(r+1) := by rw [mul_pow]
      _≤Y*(Y/q+1)^(r+1) := Nat.mul_le_mul_right _ hsize
  exact (Nat.mul_lt_mul_left hY).mp hcancel

/-- The inherited reciprocal harmonic sum is monotone at integer cutoffs. -/
theorem b593_reciprocal_harmonic_mono434 {A B : ℕ} (hAB : A≤B) :
    reciprocalHarmonic A≤ reciprocalHarmonic B := by
  unfold reciprocalHarmonic
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
      (Finset.mem_Ioc.mp hn).2.trans hAB⟩
  · intro n hn hnot
    positivity

/-- The first actual harmonic atom is retained, so H_Y≥1 for Y≥1. -/
theorem b593_reciprocal_harmonic_one_le434 (Y : ℕ) (hY : 1≤Y) :
    1≤ reciprocalHarmonic Y := by
  have hh := b593_reciprocal_harmonic_mono434 hY
  have hone : reciprocalHarmonic 1=1 := by norm_num [reciprocalHarmonic]
  rwa [hone] at hh
end Green64Analytic.SourceDivisorMoment

end

end

/-! ## AbsorbedHyperbola -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceDivisorMoment
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The actual q^(r+1)≤Y condition pays the entire lattice error
pointwise at B=Y/q. The only remaining sum is a true harmonic factor sum. -/
theorem b593_finite_unit_hyperbola_absorbed434
    (r Y q a : ℕ) (S : Finset (Fin (r+1)→ℕ))
    (hq : 0<q) (ha : q.Coprime a) (hqsize : q^(r+1)≤Y)
    (hpos : ∀x∈S,∀i,0<x i)
    (hsize : ∀x∈S,(∏i,x i)≤Y)
    (hres : ∀x∈S,Nat.ModEq q (∏i,x i) a) :
    (S.card:ℝ) ≤ (2*(r+1):ℝ)*((Y:ℝ)/(q:ℝ))*
      ∑p∈b593HyperbolaPrefixes r (Y/q),1/((∏i,p i:ℕ):ℝ) := by
  let P := b593HyperbolaPrefixes r (Y/q)
  have hmass : (P.card:ℝ) ≤ (Y:ℝ)/(q:ℝ)*
      ∑p∈P,1/((∏i,p i:ℕ):ℝ) := by
    calc
      (P.card:ℝ)=∑_p∈P,(1:ℝ) := by simp
      _≤∑p∈P,(Y:ℝ)/(q:ℝ)*(1/((∏i,p i:ℕ):ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hppos (i:Fin r) : 0<p i :=
          (Finset.mem_Ioc.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hp).1 i)).1
        have hb : 0<(∏i,p i:ℕ) := Finset.prod_pos (fun i hi=>hppos i)
        have hbr : 0<((∏i,p i:ℕ):ℝ) := by exact_mod_cast hb
        have hqr : 0<(q:ℝ) := by exact_mod_cast hq
        have hbY : (∏i,p i)*q≤Y :=
          (Nat.le_div_iff_mul_le hq).mp (Finset.mem_filter.mp hp).2
        have hdiv : (1:ℝ)≤(Y:ℝ)/(((∏i,p i:ℕ):ℝ)*(q:ℝ)) := by
          apply (le_div_iff₀ (mul_pos hbr hqr)).mpr
          simpa only [one_mul,Nat.cast_mul] using (show ((∏i,p i)*q:ℝ)≤(Y:ℝ) from by exact_mod_cast hbY)
        calc
          (1:ℝ)≤(Y:ℝ)/(((∏i,p i:ℕ):ℝ)*(q:ℝ)) := hdiv
          _=_ := by field_simp
      _=_ := (Finset.mul_sum ..).symm
  have hc := b593_finite_unit_hyperbola_real434 r Y (Y/q) q a S hq ha
    hpos hsize hres (b593_quotient_hyperbola_cutoff434 r Y q hq hqsize)
  change (S.card:ℝ)≤(r+1:ℝ)*
    ((Y:ℝ)/(q:ℝ)*(∑p∈P,1/((∏i,p i:ℕ):ℝ))+(P.card:ℝ)) at hc
  calc
    (S.card:ℝ)≤(r+1:ℝ)*
      ((Y:ℝ)/(q:ℝ)*(∑p∈P,1/((∏i,p i:ℕ):ℝ))+(P.card:ℝ)) := hc
    _≤(r+1:ℝ)*
      ((Y:ℝ)/(q:ℝ)*(∑p∈P,1/((∏i,p i:ℕ):ℝ))+
       (Y:ℝ)/(q:ℝ)*(∑p∈P,1/((∏i,p i:ℕ):ℝ))) := by
      gcongr
    _=_ := by dsimp only [P];ring
end Green64Analytic.SourceDivisorMoment

end

end

/-! ## UnitAPDivisorMoment -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceDivisorMoment
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The true sixteenfold divisor convolution in an invertible progression.
The max-factor construction, exact tuple multiplicities, and the complete
lattice error are all proved before this harmonic estimate is applied. -/
theorem b593_unit_progression_d16_harmonic434
    (Y q a : ℕ) (hq : 0<q) (ha : q.Coprime a) (hqsize : q^16≤Y) :
    (∑n∈(Finset.Ioc 0 Y).filter (fun n=>Nat.ModEq q n a),
        ((ArithmeticFunction.zeta^16) n:ℝ)) ≤
      32*((Y:ℝ)/(q:ℝ))*(reciprocalHarmonic Y)^15 := by
  let S := (b594PositiveTuples 16 Y).filter
    (fun x=>(∏i,x i)≤Y ∧ Nat.ModEq q (∏i,x i) a)
  have hpos : ∀x∈S,∀i,0<x i := by
    intro x hx i
    exact (b594_mem_positiveTuples434.mp (Finset.mem_filter.mp hx).1 i).1
  have hsize : ∀x∈S,(∏i,x i)≤Y := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2.1
  have hres : ∀x∈S,Nat.ModEq q (∏i,x i) a := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2.2
  have hcount : (S.card:ℝ) ≤ 32*((Y:ℝ)/(q:ℝ))*
      ∑p∈b593HyperbolaPrefixes 15 (Y/q),1/((∏i,p i:ℕ):ℝ) := by
    convert b593_finite_unit_hyperbola_absorbed434 15 Y q a S
      hq ha hqsize hpos hsize hres using 1; norm_num
  have hprefix : (∑p∈b593HyperbolaPrefixes 15 (Y/q),1/((∏i,p i:ℕ):ℝ)) ≤
      (reciprocalHarmonic Y)^15 := by
    calc
      _=(∑n∈Finset.Ioc 0 (Y/q),((ArithmeticFunction.zeta^15) n:ℝ)/(n:ℝ)) := by
        simpa only [b593HyperbolaPrefixes,b594PositiveTuples,mul_one_div] using
          b594_tuple_sum_by_product434 15 (Y/q) (Y/q) (le_refl _) (fun n=>1/(n:ℝ))
      _≤(reciprocalHarmonic (Y/q))^15 := by
        simpa using b593_zeta_power_harmonic434 (Y/q) 14
      _≤(reciprocalHarmonic Y)^15 :=
        pow_le_pow_left₀ (reciprocalHarmonic_nonneg (Y/q))
          (b593_reciprocal_harmonic_mono434 (Nat.div_le_self Y q)) 15
  have hidentity : (S.card:ℝ)=
      ∑n∈(Finset.Ioc 0 Y).filter (fun n=>Nat.ModEq q n a),
        ((ArithmeticFunction.zeta^16) n:ℝ) := by
    exact_mod_cast b594_tuple_progression_card434 16 Y q a
  calc
    _=(S.card:ℝ) := hidentity.symm
    _≤32*((Y:ℝ)/(q:ℝ))*
      ∑p∈b593HyperbolaPrefixes 15 (Y/q),1/((∏i,p i:ℕ):ℝ) := hcount
    _≤_ := mul_le_mul_of_nonneg_left hprefix (by positivity)

/-- Genuine all-integer fourth divisor moment in a UNIT arithmetic
progression, with the required 1/q density and constant32. This estimate
is derived without a pointwise polynomial divisor cap or an AP moment
hypothesis. It is the native arithmetic consumer required by B584. -/
theorem b593_unit_progression_tau_four434
    (Y q a : ℕ) (hq : 0<q) (ha : q.Coprime a) (hqsize : q^16≤Y) :
    (∑n∈(Finset.Ioc 0 Y).filter (fun n=>Nat.ModEq q n a),
        (n.divisors.card:ℝ)^4) ≤
      32*((Y:ℝ)/(q:ℝ))*(1+Real.log (Y:ℝ))^15 := by
  have hmajor :
      (∑n∈(Finset.Ioc 0 Y).filter (fun n=>Nat.ModEq q n a),
        (n.divisors.card:ℝ)^4) ≤
      ∑n∈(Finset.Ioc 0 Y).filter (fun n=>Nat.ModEq q n a),
        ((ArithmeticFunction.zeta^16) n:ℝ) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnpos : 0<n := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
    exact_mod_cast b593_actual_tau_four_le_d16_434 n (Nat.ne_of_gt hnpos)
  have hharm : (reciprocalHarmonic Y)^15≤(1+Real.log (Y:ℝ))^15 :=
    pow_le_pow_left₀ (reciprocalHarmonic_nonneg Y)
      (reciprocalHarmonic_le_one_add_log Y) 15
  exact hmajor.trans ((b593_unit_progression_d16_harmonic434 Y q a hq ha hqsize).trans
    (mul_le_mul_of_nonneg_left hharm (by positivity)))
end Green64Analytic.SourceDivisorMoment

end

end

