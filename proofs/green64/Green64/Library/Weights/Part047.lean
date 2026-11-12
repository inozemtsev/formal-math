module

public import Green64.Library.Correlation.Part034
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Green64.Library.Weights.Part017
public import Green64.Library.Weights.Part046
public import Green64.Library.Weights.Part043
public import Green64.Library.Weights.Part042
public import Green64.Library.Weights.Part018
public import Green64.Library.Analysis.Estimates.Part010
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
# Weights / Part047

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalC6DyadicMinorLogSaving -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Explicit TRUE arithmetic criterion yielding any desired
logarithmic minor-arc saving from the C6 integer bilinear
norm on original dyad windows P<=M, Q<=N.
Write E=L^D, ℓ=log(2r). If r,N>=E,
M>=E*ℓ and M*N>=E*r*ℓ, then the integer
large-denominator spectral factor is <=5*L^-D.
These are real scale conditions suitable for checking against
the ORIGINAL source03 moving product dyads, not a
tautological assumption that the final spectral factor
is already small. -/
theorem source_original_C6_dyadic_minor_log_saving434
    (M N P Q r : ℕ) (L D : ℝ)
    (hM : 0 < M) (hN : 0 < N) (hr : 0 < r)
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hL : 1 ≤ L)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D * Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D * (r:ℝ) * Real.log (2*(r:ℝ)) ≤
        (M:ℝ)*(N:ℝ)) :
    ((P:ℝ)+(1+(Q:ℝ)/(r:ℝ))*
        ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ)))) /
      ((M:ℝ)*(N:ℝ)) ≤ 5*L^(-D) := by
  let E : ℝ := L^D
  let lr : ℝ := Real.log (2*(r:ℝ))
  have hLp : 0 < L := by linarith
  have hEp : 0 < E := Real.rpow_pos_of_pos hLp _
  have hmp : (0:ℝ) < M := by exact_mod_cast hM
  have hnp : (0:ℝ) < N := by exact_mod_cast hN
  have hrp : (0:ℝ) < r := by exact_mod_cast hr
  have hmnp : (0:ℝ) < (M:ℝ)*(N:ℝ) := mul_pos hmp hnp
  have hInv : E⁻¹ = L^(-D) := by
    dsimp [E]
    rw [Real.rpow_neg hLp.le]
  have hOneR : (1:ℝ)/(r:ℝ) ≤ 1/E := by
    apply (div_le_div_iff₀ hrp hEp).2
    simpa only [one_mul] using hR
  have hTwoN : (2:ℝ)/(N:ℝ) ≤ 2/E := by
    apply (div_le_div_iff₀ hnp hEp).2
    nlinarith [hNlarge]
  have hLogM : lr/(M:ℝ) ≤ 1/E := by
    apply (div_le_div_iff₀ hmp hEp).2
    simpa only [E,lr,mul_comm,mul_one] using hMlarge
  have hLogMN :
      (r:ℝ)*lr/((M:ℝ)*(N:ℝ)) ≤ 1/E := by
    apply (div_le_div_iff₀ hmnp hEp).2
    nlinarith [hMNlarge]
  have hCore :=
    source_original_c6_dyadic_spectral_ratio434
      M N P Q r hM hN hr hP hQ
  dsimp only at hCore
  calc
    _ ≤ (1:ℝ)/(r:ℝ) + 2/(N:ℝ) +
         lr/(M:ℝ)+(r:ℝ)*lr/((M:ℝ)*(N:ℝ)) := hCore
    _ ≤ 5/E := by
      calc
        _ ≤ 1/E + 2/E + 1/E + 1/E :=
          add_le_add
            (add_le_add (add_le_add hOneR hTwoN) hLogM)
            hLogMN
        _ = 5/E := by ring
    _ = 5*L^(-D) := by rw [show 5/E = 5*E⁻¹ from by ring,hInv]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalC6PhysicalSpectralSquare -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Quantitative C6 arithmetic spectral saving transferred
to the ACTUAL squared physical Hilbert norm scale.
Unlike a generic L∞ bound, A and B are the true
nonnegative per-group factorial prime-atom prefactors,
and EA,EB are arbitrary L² endpoint energies.
Once the window spectral ratio T/(MN) <= 5 L^-D,
the EXACT C6 square root expression is <=
  125 A B EA EB L^-D.
This algebraic lemma ensures no implicit √(#atoms) loss. -/
theorem source_original_C6_physical_spectral_square434
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (A B EA EB T L D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hEA : 0 ≤ EA) (hEB : 0 ≤ EB)
    (hT : 0 ≤ T)
    (hRatio : T/((M:ℝ)*(N:ℝ)) ≤ 5*L^(-D)) :
    (5*Real.sqrt (((1/(M:ℝ))*A)*EA)*
       Real.sqrt (((1/(N:ℝ))*B)*EB)*
       Real.sqrt T)^2 ≤
       125*(A*B)*(EA*EB)*L^(-D) := by
  have hMp : (0:ℝ) < M := by exact_mod_cast hM
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hRA : 0 ≤ ((1/(M:ℝ))*A)*EA := by positivity
  have hRB : 0 ≤ ((1/(N:ℝ))*B)*EB := by positivity
  have hSq :
      (5*Real.sqrt (((1/(M:ℝ))*A)*EA)*
           Real.sqrt (((1/(N:ℝ))*B)*EB)*Real.sqrt T)^2 =
      25*(((1/(M:ℝ))*A)*EA)*
         (((1/(N:ℝ))*B)*EB)*T := by
    simp only [mul_pow, Real.sq_sqrt hRA,
      Real.sq_sqrt hRB,Real.sq_sqrt hT]
    ring
  have hExpr :
      25*(((1/(M:ℝ))*A)*EA)*
         (((1/(N:ℝ))*B)*EB)*T =
      25*(A*B)*(EA*EB)*
        (T/((M:ℝ)*(N:ℝ))) := by
    field_simp [ne_of_gt hMp, ne_of_gt hNp]
  have hCoeff : 0 ≤ 25*(A*B)*(EA*EB) := by positivity
  calc
    _ = 25*(A*B)*(EA*EB)*(T/((M:ℝ)*(N:ℝ))) := by
      rw [hSq,hExpr]
    _ ≤ (25*(A*B)*(EA*EB))*(5*L^(-D)) :=
      mul_le_mul_of_nonneg_left hRatio hCoeff
    _ = 125*(A*B)*(EA*EB)*L^(-D) := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualC6PhysicalMinorLogPower -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Original SOURCE03 true grouped independently labelled
BIG prime-product C6 minor circle bound, squared-L2 and
with EXPLICIT log-power saving. The authentic C6 phase,
atomic harmonic laws and sharp GROUP-WISE factorial costs
remain unchanged. Assume only the actual integer dyad
windows P≤M, Q≤N, positive denominator r and concrete
scale lower bounds r,N≥L^D, M≥L^D log(2r),
M*N≥L^D*r*log(2r). Then for arbitrary mark-dependent
complex endpoint tests the actual squared phase sum is
<=125*prefA*prefB*EA*EB*L^-D.
This is the authentic physical C6 estimate under
arithmetic scale assumptions, not a proof yet that the
original moving source03 ranges satisfy all of them. -/
theorem source_original_actual_C6_minor_physical_log_power434
    {γA γB : Type} [DecidableEq γA] [DecidableEq γB]
    (GA : Finset γA) (SA : γA → Finset ℕ)
    (kA : γA → ℕ) (VA : γA → ℝ)
    (GB : Finset γB) (SB : γB → Finset ℕ)
    (kB : γB → ℕ) (VB : γB → ℝ)
    (hPrimeA : ∀ g∈GA, ∀ p∈SA g, p.Prime)
    (hPrimeB : ∀ g∈GB, ∀ p∈SB g, p.Prime)
    (hDisjointA : ∀ g∈GA, ∀ h∈GA, g≠h →
        Disjoint (SA g) (SA h))
    (hDisjointB : ∀ g∈GB, ∀ h∈GB, g≠h →
        Disjoint (SB g) (SB h))
    (hVA : ∀ g∈GA, 0 < VA g)
    (hVB : ∀ g∈GB, 0 < VB g)
    (fA : SourceOriginalGramPrimeTuple434
      (fun z : Σ g : GA, Fin (kA g.val) => SA z.1.val) → ℂ)
    (fB : SourceOriginalGramPrimeTuple434
      (fun z : Σ g : GB, Fin (kB g.val) => SB z.1.val) → ℂ)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (L D : ℝ) (hL : 1 ≤ L)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
        (M:ℝ)*(N:ℝ)) :
    let PA : (Σ g : GA, Fin (kA g.val)) → Finset ℕ :=
      fun z => SA z.1.val
    let PB : (Σ g : GB, Fin (kB g.val)) → Finset ℕ :=
      fun z => SB z.1.val
    let muA : (Σ g : GA, Fin (kA g.val)) → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(VA z.1.val)
    let muB : (Σ g : GB, Fin (kB g.val)) → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(VB z.1.val)
    let prefA := Green64SourceC6.sourceProductAtomPrefactor GA kA VA
    let prefB := Green64SourceC6.sourceProductAtomPrefactor GB kB VB
    let EA : ℝ := ∑ x : SourceOriginalGramPrimeTuple434 PA,
      sourceOriginalGramPrimeMass434 PA muA x * ‖fA x‖^2
    let EB : ℝ := ∑ y : SourceOriginalGramPrimeTuple434 PB,
      sourceOriginalGramPrimeMass434 PB muB y * ‖fB y‖^2
    ‖(∑ i ∈ Finset.range P,
        sourceOriginalPhysicalProductAtomCoefficient434 PA muA fA (M+i) *
       (∑ j ∈ Finset.range Q,
        sourceOriginalPhysicalProductAtomCoefficient434 PB muB fB (N+j) *
        Green64SourceC6.integerPhase
          (((a:ℝ)/(r:ℝ)+beta)*((N+j:ℕ):ℝ)) ((M+i:ℕ):ℤ)))‖^2 ≤
      125*(prefA*prefB)*(EA*EB)*L^(-D) := by
  classical
  let PA : (Σ g : GA, Fin (kA g.val)) → Finset ℕ :=
    fun z => SA z.1.val
  let PB : (Σ g : GB, Fin (kB g.val)) → Finset ℕ :=
    fun z => SB z.1.val
  let muA : (Σ g : GA, Fin (kA g.val)) → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(VA z.1.val)
  let muB : (Σ g : GB, Fin (kB g.val)) → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(VB z.1.val)
  let prefA := Green64SourceC6.sourceProductAtomPrefactor GA kA VA
  let prefB := Green64SourceC6.sourceProductAtomPrefactor GB kB VB
  let EA : ℝ := ∑ x : SourceOriginalGramPrimeTuple434 PA,
    sourceOriginalGramPrimeMass434 PA muA x*‖fA x‖^2
  let EB : ℝ := ∑ y : SourceOriginalGramPrimeTuple434 PB,
    sourceOriginalGramPrimeMass434 PB muB y*‖fB y‖^2
  let T : ℝ := (P:ℝ)+(1+(Q:ℝ)/(r:ℝ))*
    ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ)))
  have hPA : 0 ≤ prefA := by
    dsimp [prefA, Green64SourceC6.sourceProductAtomPrefactor]
    apply Finset.prod_nonneg
    intro g hg
    exact div_nonneg (by positivity)
      (pow_nonneg (hVA g hg).le _)
  have hPB : 0 ≤ prefB := by
    dsimp [prefB, Green64SourceC6.sourceProductAtomPrefactor]
    apply Finset.prod_nonneg
    intro g hg
    exact div_nonneg (by positivity)
      (pow_nonneg (hVB g hg).le _)
  have hmuA (x : SourceOriginalGramPrimeTuple434 PA) :
      0 ≤ sourceOriginalGramPrimeMass434 PA muA x := by
    unfold sourceOriginalGramPrimeMass434
    apply Finset.prod_nonneg
    intro i hi
    dsimp [muA]
    exact div_nonneg (by positivity) (hVA i.1.val i.1.property).le
  have hmuB (x : SourceOriginalGramPrimeTuple434 PB) :
      0 ≤ sourceOriginalGramPrimeMass434 PB muB x := by
    unfold sourceOriginalGramPrimeMass434
    apply Finset.prod_nonneg
    intro i hi
    dsimp [muB]
    exact div_nonneg (by positivity) (hVB i.1.val i.1.property).le
  have hEA : 0 ≤ EA := by
    dsimp [EA]
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (hmuA x) (sq_nonneg _)
  have hEB : 0 ≤ EB := by
    dsimp [EB]
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (hmuB x) (sq_nonneg _)
  have hRone : (1:ℝ) ≤ (r:ℝ) := by
    have hh : 1 ≤ r := by omega
    exact_mod_cast hh
  have hLog : 0 ≤ Real.log (2*(r:ℝ)) := by
    apply Real.log_nonneg
    nlinarith
  have hrpos : (0:ℝ) < r := by exact_mod_cast hr
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  have hRatio : T/((M:ℝ)*(N:ℝ)) ≤ 5*L^(-D) := by
    exact source_original_C6_dyadic_minor_log_saving434
      M N P Q r L D hM hN hr hP hQ
      hL hR hNlarge hMlarge hMNlarge
  have hActual := source_original_actual_C6_minor_physical_energy434
    GA SA kA VA GB SB kB VB
    hPrimeA hPrimeB hDisjointA hDisjointB hVA hVB
    fA fB M N P Q hM hN a r beta hr hcop hbeta
  have hSquare :=
    source_original_C6_physical_spectral_square434
      M N hM hN prefA prefB EA EB T L D
      hPA hPB hEA hEB hT hRatio
  change
    ‖(∑ i ∈ Finset.range P,
      sourceOriginalPhysicalProductAtomCoefficient434 PA muA fA (M+i) *
        (∑ j ∈ Finset.range Q,
          sourceOriginalPhysicalProductAtomCoefficient434 PB muB fB (N+j) *
          Green64SourceC6.integerPhase
            (((a:ℝ)/(r:ℝ)+beta)*((N+j:ℕ):ℝ))
            ((M+i:ℕ):ℤ)))‖^2 ≤
       125*(prefA*prefB)*(EA*EB)*L^(-D)
  exact (pow_le_pow_left₀ (norm_nonneg _) hActual 2).trans hSquare
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalC6GroupFactorialBudget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- TRUE grouped SOURCE03 C6 factorial prefactor has a
uniform per-group bound when each original group has at most
m0 independently labelled prime slots and true normalizer
V_g >= Vmin>0. The bound grows as
 [m0! * max(1,Vmin^-1)^m0]^(#original groups)
rather than factorial(total number of prime slots).
This is the exact quantitative factor to compare with the
original O(log L) number of moving BIG groups. No normalization
or bounded-group-count hypothesis is silently inferred. -/
theorem source_original_c6_group_factorial_uniform_bound434
    {γ : Type} [DecidableEq γ]
    (G : Finset γ) (k : γ → ℕ) (V : γ → ℝ)
    (m0 : ℕ) (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hk : ∀ g∈G, k g ≤ m0)
    (hV : ∀ g∈G, Vmin ≤ V g) :
    Green64SourceC6.sourceProductAtomPrefactor G k V ≤
      (((m0.factorial:ℕ):ℝ)*
         (max (1:ℝ) Vmin⁻¹)^m0)^G.card := by
  classical
  let A : ℝ := ((m0.factorial:ℕ):ℝ)*
    (max (1:ℝ) Vmin⁻¹)^m0
  have hFloor : (0:ℝ) ≤ max (1:ℝ) Vmin⁻¹ :=
    (by linarith : (0:ℝ) ≤ 1).trans (le_max_left _ _)
  have hFactor (g : γ) (hg : g∈G) :
      (((k g).factorial:ℕ):ℝ)/(V g)^(k g) ≤ A := by
    have hVg : 0 < V g := hVmin.trans_le (hV g hg)
    have hInv : (V g)⁻¹ ≤ Vmin⁻¹ :=
      (inv_le_inv₀ hVg hVmin).2 (hV g hg)
    have hInvBound : (V g)⁻¹ ≤ max (1:ℝ) Vmin⁻¹ :=
      hInv.trans (le_max_right _ _)
    have hFact : (((k g).factorial:ℕ):ℝ) ≤
        (((m0.factorial:ℕ):ℝ)) := by
      exact_mod_cast Nat.factorial_le (hk g hg)
    have hPow :
        ((V g)⁻¹)^(k g) ≤
           (max (1:ℝ) Vmin⁻¹)^m0 := by
      calc
        _ ≤ (max (1:ℝ) Vmin⁻¹)^(k g) :=
          pow_le_pow_left₀ (inv_nonneg.mpr hVg.le) hInvBound _
        _ ≤ (max (1:ℝ) Vmin⁻¹)^m0 :=
          pow_le_pow_right₀ (le_max_left _ _) (hk g hg)
    dsimp [A]
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_le_mul hFact hPow
      (pow_nonneg (inv_nonneg.mpr hVg.le) _) (Nat.cast_nonneg _)
  calc
    _ = ∏ g : G,
          ((((k g.val).factorial:ℕ):ℝ)/(V g.val)^(k g.val)) := by
      unfold Green64SourceC6.sourceProductAtomPrefactor
      exact (Finset.prod_attach G
        (fun g => ((((k g).factorial:ℕ):ℝ)/(V g)^(k g)))).symm
    _ ≤ ∏ _g : G, A := by
      apply Finset.prod_le_prod₀
      · intro g hg
        exact div_nonneg (Nat.cast_nonneg _)
          (pow_nonneg (hVmin.trans_le (hV g.val g.property)).le _)
      · intro g hg
        exact hFactor g.val g.property
    _ = A^G.card := by
      simp only [Finset.prod_const, Finset.card_univ,
        Fintype.card_coe]
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalC6GroupPrefactorLog -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The TRUE source03 grouped C6 factorial prefactor is at
most a FIXED log-power L^C whenever the exact genuine
number of moving BIG groups G, fixed slot cap m0 and
positive normalizer Vmin satisfy the explicit quantitative
group-count budget:
  card(G) * log(m0! * max(1,Vmin^-1)^m0) <= C*log L.
This exposes precisely the group-number arithmetic condition
rather than assuming the factorial prefactor itself is
polynomial. The per-group factorial bound is proved in C253. -/
theorem source_original_c6_group_prefactor_log_power434
    {γ : Type} [DecidableEq γ]
    (G : Finset γ) (k : γ → ℕ) (V : γ → ℝ)
    (m0 C : ℕ) (Vmin L : ℝ)
    (hVmin : 0 < Vmin) (hL : 1 ≤ L)
    (hk : ∀ g∈G, k g ≤ m0)
    (hV : ∀ g∈G, Vmin ≤ V g)
    (hGroup :
      (G.card:ℝ)*
       Real.log (((m0.factorial:ℕ):ℝ)*
         (max (1:ℝ) Vmin⁻¹)^m0) ≤
      (C:ℝ)*Real.log L) :
    Green64SourceC6.sourceProductAtomPrefactor G k V ≤
      L^C := by
  let A : ℝ := ((m0.factorial:ℕ):ℝ)*
    (max (1:ℝ) Vmin⁻¹)^m0
  have hFact : (0:ℝ) < ((m0.factorial:ℕ):ℝ) := by
    exact_mod_cast Nat.factorial_pos m0
  have hFloor : (0:ℝ) < max (1:ℝ) Vmin⁻¹ :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hApos : 0 < A := by
    dsimp [A]
    exact mul_pos hFact (pow_pos hFloor _)
  have hLp : 0 < L := by linarith
  have hPower : A^G.card ≤ L^C := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast,
      Real.rpow_def_of_pos hApos, Real.rpow_def_of_pos hLp]
    exact Real.exp_le_exp.mpr (by
      simpa only [A, mul_comm] using hGroup)
  exact (source_original_c6_group_factorial_uniform_bound434
     G k V m0 Vmin hVmin hk hV).trans hPower
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalC6GroupLossAbsorb -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Quantitative SOURCE03 arithmetic saving absorption:
If the TRUE C6 group factorial prefactors cost at most
L^CA and L^CB, and the C6 integer bilinear saving is L^-D,
then spending D>=B+CA+CB yields the target true physical
squared-L2 error O(L^-B), with NO prime support size
loss. All original numerical factors are explicit.
This does not assume factorial prefactors are polynomial:
that claim is separately checked under group-count geometry
in C254. -/
theorem source_original_c6_group_loss_absorb434
    (L B D : ℝ) (CA CB : ℕ)
    (hL : 1 ≤ L)
    (hSave : B+(CA:ℝ)+(CB:ℝ) ≤ D)
    (A Bpref EA EB : ℝ)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ Bpref)
    (hEA : 0 ≤ EA) (hEB : 0 ≤ EB)
    (hAp : A ≤ L^CA) (hBp : Bpref ≤ L^CB) :
    125*(A*Bpref)*(EA*EB)*L^(-D) ≤
      125*(EA*EB)*L^(-B) := by
  have hLp : 0 < L := by linarith
  have hLnn : 0 ≤ L := hLp.le
  have hAB : A*Bpref ≤ L^CA*L^CB :=
    mul_le_mul hAp hBp hB0 (pow_nonneg hLnn _)
  have hSpectral : L^((CA:ℝ)+(CB:ℝ))*L^(-D) ≤ L^(-B) := by
    rw [← Real.rpow_add hLp]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hABPow : L^CA*L^CB =
      L^((CA:ℝ)+(CB:ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_add hLp]
  have hProd :
      A*Bpref*L^(-D) ≤ L^(-B) := by
    calc
      _ ≤ (L^CA*L^CB)*L^(-D) :=
        mul_le_mul_of_nonneg_right hAB
          (Real.rpow_nonneg hLnn _)
      _ = L^((CA:ℝ)+(CB:ℝ))*L^(-D) := by rw [hABPow]
      _ ≤ L^(-B) := hSpectral
  have hEnergy : 0 ≤ 125*(EA*EB) := by positivity
  calc
    _ = (125*(EA*EB))*(A*Bpref*L^(-D)) := by ring
    _ ≤ (125*(EA*EB))*L^(-B) :=
      mul_le_mul_of_nonneg_left hProd hEnergy
    _ = 125*(EA*EB)*L^(-B) := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualC6PhysicalMinorAbsorbed -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- Fully quantified TRUE physical C6 SOURCE03 minor arc
L² LOG-SAVING for actual disjoint grouped independently
labelled prime marks, arbitrary complex mark-dependent
test functions and original integerPhase convention.
Actual group-wise factorial atom constants are *proved*
polynomial from fixed mark cap m0, lower normalizer Vmin
and explicit original group-count logarithmic bounds, then
absorbed by spending CA+CB of the true integer C6
spectral saving D.
No mass-envelope, bounded-test, or desired L^-B bound
is assumed. The moving original groups and integer windows
must satisfy the stated genuine arithmetic premises; the
ν-pattern and full four-channel assembly are not proved here. -/
theorem source_original_actual_C6_minor_log_power_after_group_budget434
    {γA γB : Type} [DecidableEq γA] [DecidableEq γB]
    (GA : Finset γA) (SA : γA → Finset ℕ)
    (kA : γA → ℕ) (VA : γA → ℝ)
    (GB : Finset γB) (SB : γB → Finset ℕ)
    (kB : γB → ℕ) (VB : γB → ℝ)
    (hPrimeA : ∀ g∈GA, ∀ p∈SA g, p.Prime)
    (hPrimeB : ∀ g∈GB, ∀ p∈SB g, p.Prime)
    (hDisjointA : ∀ g∈GA, ∀ h∈GA, g≠h →
        Disjoint (SA g) (SA h))
    (hDisjointB : ∀ g∈GB, ∀ h∈GB, g≠h →
        Disjoint (SB g) (SB h))
    (hVA : ∀ g∈GA, 0 < VA g)
    (hVB : ∀ g∈GB, 0 < VB g)
    (fA : SourceOriginalGramPrimeTuple434
      (fun z : Σ g : GA, Fin (kA g.val) => SA z.1.val) → ℂ)
    (fB : SourceOriginalGramPrimeTuple434
      (fun z : Σ g : GB, Fin (kB g.val) => SB z.1.val) → ℂ)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (L D : ℝ) (hL : 1 ≤ L)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
        (M:ℝ)*(N:ℝ))
    (Bsave : ℝ) (m0 CA CB : ℕ)
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hKA : ∀ g∈GA, kA g ≤ m0)
    (hKB : ∀ g∈GB, kB g ≤ m0)
    (hVAmin : ∀ g∈GA, Vmin ≤ VA g)
    (hVBmin : ∀ g∈GB, Vmin ≤ VB g)
    (hGroupA :
      (GA.card:ℝ)*Real.log (((m0.factorial:ℕ):ℝ)*
        (max (1:ℝ) Vmin⁻¹)^m0) ≤
        (CA:ℝ)*Real.log L)
    (hGroupB :
      (GB.card:ℝ)*Real.log (((m0.factorial:ℕ):ℝ)*
        (max (1:ℝ) Vmin⁻¹)^m0) ≤
        (CB:ℝ)*Real.log L)
    (hSaving : Bsave+(CA:ℝ)+(CB:ℝ) ≤ D) :
    let PA : (Σ g : GA, Fin (kA g.val)) → Finset ℕ :=
      fun z => SA z.1.val
    let PB : (Σ g : GB, Fin (kB g.val)) → Finset ℕ :=
      fun z => SB z.1.val
    let muA : (Σ g : GA, Fin (kA g.val)) → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(VA z.1.val)
    let muB : (Σ g : GB, Fin (kB g.val)) → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(VB z.1.val)
    let prefA := Green64SourceC6.sourceProductAtomPrefactor GA kA VA
    let prefB := Green64SourceC6.sourceProductAtomPrefactor GB kB VB
    let EA : ℝ := ∑ x : SourceOriginalGramPrimeTuple434 PA,
      sourceOriginalGramPrimeMass434 PA muA x * ‖fA x‖^2
    let EB : ℝ := ∑ y : SourceOriginalGramPrimeTuple434 PB,
      sourceOriginalGramPrimeMass434 PB muB y * ‖fB y‖^2
    ‖(∑ i ∈ Finset.range P,
        sourceOriginalPhysicalProductAtomCoefficient434 PA muA fA (M+i) *
       (∑ j ∈ Finset.range Q,
        sourceOriginalPhysicalProductAtomCoefficient434 PB muB fB (N+j) *
        Green64SourceC6.integerPhase
          (((a:ℝ)/(r:ℝ)+beta)*((N+j:ℕ):ℝ)) ((M+i:ℕ):ℤ)))‖^2 ≤
      125*(EA*EB)*L^(-Bsave) := by
  classical
  let PA : (Σ g : GA, Fin (kA g.val)) → Finset ℕ :=
    fun z => SA z.1.val
  let PB : (Σ g : GB, Fin (kB g.val)) → Finset ℕ :=
    fun z => SB z.1.val
  let muA : (Σ g : GA, Fin (kA g.val)) → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(VA z.1.val)
  let muB : (Σ g : GB, Fin (kB g.val)) → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(VB z.1.val)
  let prefA := Green64SourceC6.sourceProductAtomPrefactor GA kA VA
  let prefB := Green64SourceC6.sourceProductAtomPrefactor GB kB VB
  let EA : ℝ := ∑ x : SourceOriginalGramPrimeTuple434 PA,
    sourceOriginalGramPrimeMass434 PA muA x*‖fA x‖^2
  let EB : ℝ := ∑ y : SourceOriginalGramPrimeTuple434 PB,
    sourceOriginalGramPrimeMass434 PB muB y*‖fB y‖^2
  let T : ℝ := (P:ℝ)+(1+(Q:ℝ)/(r:ℝ))*
    ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ)))
  have hPA : 0 ≤ prefA := by
    dsimp [prefA, Green64SourceC6.sourceProductAtomPrefactor]
    apply Finset.prod_nonneg
    intro g hg
    exact div_nonneg (by positivity)
      (pow_nonneg (hVA g hg).le _)
  have hPB : 0 ≤ prefB := by
    dsimp [prefB, Green64SourceC6.sourceProductAtomPrefactor]
    apply Finset.prod_nonneg
    intro g hg
    exact div_nonneg (by positivity)
      (pow_nonneg (hVB g hg).le _)
  have hmuA (x : SourceOriginalGramPrimeTuple434 PA) :
      0 ≤ sourceOriginalGramPrimeMass434 PA muA x := by
    unfold sourceOriginalGramPrimeMass434
    apply Finset.prod_nonneg
    intro i hi
    dsimp [muA]
    exact div_nonneg (by positivity) (hVA i.1.val i.1.property).le
  have hmuB (x : SourceOriginalGramPrimeTuple434 PB) :
      0 ≤ sourceOriginalGramPrimeMass434 PB muB x := by
    unfold sourceOriginalGramPrimeMass434
    apply Finset.prod_nonneg
    intro i hi
    dsimp [muB]
    exact div_nonneg (by positivity) (hVB i.1.val i.1.property).le
  have hEA : 0 ≤ EA := by
    dsimp [EA]
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (hmuA x) (sq_nonneg _)
  have hEB : 0 ≤ EB := by
    dsimp [EB]
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (hmuB x) (sq_nonneg _)
  have hRaw := source_original_actual_C6_minor_physical_log_power434
    GA SA kA VA GB SB kB VB
    hPrimeA hPrimeB hDisjointA hDisjointB hVA hVB
    fA fB M N P Q hM hN a r beta hr hcop hbeta
    hP hQ L D hL hR hNlarge hMlarge hMNlarge
  have hFactorA :=
    source_original_c6_group_prefactor_log_power434
      GA kA VA m0 CA Vmin L hVmin hL
      hKA hVAmin hGroupA
  have hFactorB :=
    source_original_c6_group_prefactor_log_power434
      GB kB VB m0 CB Vmin L hVmin hL
      hKB hVBmin hGroupB
  have hAbsorb :=
    source_original_c6_group_loss_absorb434
      L Bsave D CA CB hL hSaving prefA prefB EA EB
      hPA hPB hEA hEB hFactorA hFactorB
  change
    ‖(∑ i ∈ Finset.range P,
      sourceOriginalPhysicalProductAtomCoefficient434 PA muA fA (M+i) *
        (∑ j ∈ Finset.range Q,
          sourceOriginalPhysicalProductAtomCoefficient434 PB muB fB (N+j) *
          Green64SourceC6.integerPhase
            (((a:ℝ)/(r:ℝ)+beta)*((N+j:ℕ):ℝ))
            ((M+i:ℕ):ℤ)))‖^2 ≤
       125*(EA*EB)*L^(-Bsave)
  exact hRaw.trans hAbsorb
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalC6MinorLargeProducts -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- SOURCE03 C6 integer bilinear minor-circle scale budget
without four separate interval lower bounds:
If r>=L^D and the original B-block dyadic product N>=L^D,
while the original A-block dyadic product M is at least
2*L^D*r², then every boundary term from the C6 exact
spectral norm is O(L^-D). The only new analytic input
is the unconditional elementary log(2r)<=2r bound.
This reduces the genuine minor-arc geometric prerequisites
to three checkable large-product inequalities, preserving
actual r and integer windows, not a synthetic epsilon. -/
theorem source_original_C6_minor_large_product_saving434
    (M N P Q r : ℕ) (L D : ℝ)
    (hM : 0 < M) (hN : 0 < N) (hr : 0 < r)
    (hP : P ≤ M) (hQ : Q ≤ N)
    (hL : 1 ≤ L) (hD : 0 ≤ D)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMstrong : 2*L^D*(r:ℝ)^2 ≤ (M:ℝ)) :
    ((P:ℝ)+(1+(Q:ℝ)/(r:ℝ))*
        ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ)))) /
      ((M:ℝ)*(N:ℝ)) ≤ 5*L^(-D) := by
  let E : ℝ := L^D
  let rr : ℝ := r
  let mr : ℝ := M
  let nr : ℝ := N
  let lr : ℝ := Real.log (2*rr)
  have hrp : 0 < rr := by simpa only [rr] using (by exact_mod_cast hr : (0:ℝ) < (r:ℝ))
  have hmp : 0 < mr := by simpa only [mr] using (by exact_mod_cast hM : (0:ℝ) < (M:ℝ))
  have hnp : 0 < nr := by simpa only [nr] using (by exact_mod_cast hN : (0:ℝ) < (N:ℝ))
  have hE : 0 ≤ E := Real.rpow_nonneg (by linarith : 0 ≤ L) _
  have hrl : 1 ≤ rr := by
    have hn : 1 ≤ r := by omega
    simpa only [rr] using (by exact_mod_cast hn : (1:ℝ) ≤ (r:ℝ))
  have hlog : lr ≤ 2*rr := by
    dsimp [lr]
    have hh : 0 < 2*rr := by positivity
    have he := Real.log_le_sub_one_of_pos hh
    linarith
  have hMlog : E*lr ≤ mr := by
    have h1 := mul_le_mul_of_nonneg_left hlog hE
    have hrSq : rr ≤ rr^2 := by
      nlinarith [mul_nonneg hrp.le (sub_nonneg.mpr hrl)]
    have h2 : 2*E*rr ≤ 2*E*rr^2 := by
      nlinarith [mul_le_mul_of_nonneg_left hrSq (by positivity : 0 ≤ 2*E)]
    have h3 : 2*E*rr^2 ≤ mr := hMstrong
    nlinarith
  have hMNlog : E*rr*lr ≤ mr*nr := by
    have h1 : E*rr*lr ≤ 2*E*rr^2 := by
      have hh := mul_le_mul_of_nonneg_left hlog
        (mul_nonneg hE hrp.le)
      nlinarith
    have h2 : mr ≤ mr*nr := by
      have hn : 1 ≤ nr := by
        have hnN : 1 ≤ N := by omega
        simpa only [nr] using (by exact_mod_cast hnN : (1:ℝ) ≤ (N:ℝ))
      nlinarith [mul_nonneg hmp.le (sub_nonneg.mpr hn)]
    nlinarith [hMstrong]
  exact source_original_C6_dyadic_minor_log_saving434
    M N P Q r L D hM hN hr hP hQ hL hR hNlarge
      hMlog hMNlog
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalC6ActualBoundaryLogScales -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The actual original C6 integer exponential sum's
THREE separate boundary-term scale inequalities,
without referring to a completed spectral saving.
This connects the two checkable dyadic product scales
N>=L^D and M>=2L^D*r² to precisely the hypotheses
used by the true SOURCE03 grouped physical C6 Hilbert
L² arithmetic estimate. Unlike merely bounding the
spectral ratio, these are the *exact* unmodified
hNlarge,hMlarge,hMNlarge prerequisites of C256/C268. -/
theorem source_original_C6_actual_boundary_log_scales434
    (M N r : ℕ) (L D : ℝ)
    (hM : 0 < M) (hN : 0 < N) (hr : 0 < r)
    (hL : 1 ≤ L)
    (hNlarge : L^D ≤ (N:ℝ))
    (hMstrong : 2*L^D*(r:ℝ)^2 ≤ (M:ℝ)) :
    (L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ)) ∧
    (L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
       (M:ℝ)*(N:ℝ)) := by
  let E : ℝ := L^D
  let rr : ℝ := r
  let mr : ℝ := M
  let nr : ℝ := N
  let lr : ℝ := Real.log (2*rr)
  have hrp : 0 < rr := by
    simpa only [rr] using (by exact_mod_cast hr : (0:ℝ)<(r:ℝ))
  have hmp : 0 < mr := by
    simpa only [mr] using (by exact_mod_cast hM : (0:ℝ)<(M:ℝ))
  have hnp : 0 < nr := by
    simpa only [nr] using (by exact_mod_cast hN : (0:ℝ)<(N:ℝ))
  have hE : 0 ≤ E := Real.rpow_nonneg (by linarith : 0 ≤ L) _
  have hrl : 1 ≤ rr := by
    have hn : 1 ≤ r := by omega
    simpa only [rr] using (by exact_mod_cast hn : (1:ℝ) ≤ (r:ℝ))
  have hlog : lr ≤ 2*rr := by
    dsimp [lr]
    have hh : 0 < 2*rr := by positivity
    have he := Real.log_le_sub_one_of_pos hh
    linarith
  have hrSq : rr ≤ rr^2 := by
    nlinarith [mul_nonneg hrp.le (sub_nonneg.mpr hrl)]
  have hMlog : E*lr ≤ mr := by
    have h1 := mul_le_mul_of_nonneg_left hlog hE
    have h2 := mul_le_mul_of_nonneg_left hrSq
      (by positivity : 0 ≤ 2*E)
    nlinarith [hMstrong]
  have hMNlog : E*rr*lr ≤ mr*nr := by
    have h1 : E*rr*lr ≤ 2*E*rr^2 := by
      have hh := mul_le_mul_of_nonneg_left hlog
        (mul_nonneg hE hrp.le)
      nlinarith
    have h2 : mr ≤ mr*nr := by
      have hn : 1 ≤ nr := by
        have hnN : 1 ≤ N := by omega
        simpa only [nr] using (by exact_mod_cast hnN : (1:ℝ) ≤ (N:ℝ))
      nlinarith [mul_nonneg hmp.le (sub_nonneg.mpr hn)]
    nlinarith [hMstrong]
  exact ⟨hMlog,hMNlog⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitivePairCommonModulus -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- Exact common level of TWO genuine original primitive
characters; this is at most the product q1*q2<=Q². -/
noncomputable def sourceOriginalPrimitiveCommonLevel434
    (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)) : ℕ :=
  Nat.lcm (c.1.val+1) (d.1.val+1)

/-- At the genuine common level lcm(q1,q2), equality of
two primitive characters forces their ORIGINAL conductors
equal. No additional induction-uniqueness assumption. -/
theorem source_original_primitive_lifts_equal_level434
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (χ : DirichletCharacter ℂ n)
    (ψ : DirichletCharacter ℂ m)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (hLift : (DirichletCharacter.changeLevel
      (Nat.dvd_lcm_left n m)) χ =
       (DirichletCharacter.changeLevel
      (Nat.dvd_lcm_right n m)) ψ) : n = m := by
  haveI : NeZero (Nat.lcm n m) :=
    ⟨Nat.lcm_ne_zero (Nat.ne_of_gt hn) (Nat.ne_of_gt hm)⟩
  have hc := congrArg DirichletCharacter.conductor hLift
  rw [DirichletCharacter.conductor_changeLevel χ,
      DirichletCharacter.conductor_changeLevel ψ] at hc
  exact (DirichletCharacter.isPrimitive_def χ).mp hχ ▸
    (DirichletCharacter.isPrimitive_def ψ).mp hψ ▸ hc

/-- Actual distinct original primitive character PAIRS cannot
have equal lifts to the genuine common level. Consequently
their quotient is NONPRINCIPAL, the exact arithmetic entry
condition required before the real source SW bound. -/
theorem source_original_primitive_pair_lifts_distinct434
    (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d) :
    (DirichletCharacter.changeLevel
      (Nat.dvd_lcm_left (c.1.val+1) (d.1.val+1))) c.2 ≠
    (DirichletCharacter.changeLevel
      (Nat.dvd_lcm_right (c.1.val+1) (d.1.val+1))) d.2 := by
  intro he
  have hn := source_original_primitive_lifts_equal_level434
    (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) c.2 d.2
    ((source_original_actual_primitive_mem434 Q c).mp hc)
    ((source_original_actual_primitive_mem434 Q d).mp hd) he
  have hq : c.1 = d.1 := Fin.ext (Nat.succ.inj hn)
  rcases c with ⟨qc,χ⟩
  rcases d with ⟨qd,ψ⟩
  change qc = qd at hq
  subst qd
  haveI : NeZero (Nat.lcm (qc.val+1) (qc.val+1)) :=
    ⟨Nat.lcm_ne_zero (Nat.succ_ne_zero _) (Nat.succ_ne_zero _)⟩
  have hchi : χ = ψ :=
    (DirichletCharacter.changeLevel_injective
      (Nat.dvd_lcm_left (qc.val+1) (qc.val+1))) he
  exact hne (by simp [hchi])
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitivePairQuotient -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- ORIGINAL common modulus of the two primitive
Dirichlet characters in the source03 comparison Gram. -/
noncomputable def sourceOriginalPrimitivePairQuotient434
    (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)) :
    DirichletCharacter ℂ
      (sourceOriginalPrimitiveCommonLevel434 Q c d) :=
  ((DirichletCharacter.changeLevel
      (Nat.dvd_lcm_left (c.1.val+1) (d.1.val+1))) c.2)⁻¹ *
  (DirichletCharacter.changeLevel
      (Nat.dvd_lcm_right (c.1.val+1) (d.1.val+1))) d.2

/-- The common actual conductor level is bounded by Q²
without enlarging the source comparison family or
requiring an invented fixed common modulus. -/
theorem source_original_primitive_common_level_le_square434
    (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)) :
    sourceOriginalPrimitiveCommonLevel434 Q c d ≤ Q^2 := by
  unfold sourceOriginalPrimitiveCommonLevel434
  have hc : c.1.val+1 ≤ Q := by omega
  have hd : d.1.val+1 ≤ Q := by omega
  calc
    (c.1.val+1).lcm (d.1.val+1) ≤
      (c.1.val+1)*(d.1.val+1) :=
        Nat.lcm_le_mul (Nat.zero_lt_succ _)
          (Nat.zero_lt_succ _)
    _ ≤ Q*Q := Nat.mul_le_mul hc hd
    _ = Q^2 := by ring

/-- This is the ACTUAL crucial arithmetic observation in
source03: two DISTINCT primitive complex Dirichlet chars
(with possibly different conductors) determine a NONTRIVIAL
character of the true common modulus lcm(qχ,qψ)≤Q².
No assumption of nonprincipality is made; it is proved
from true primitive conductor uniqueness and level injectivity. -/
theorem source_original_distinct_primitive_pair_quotient_nonprincipal434
    (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d) :
    sourceOriginalPrimitivePairQuotient434 Q c d ≠ 1 := by
  intro hh
  have hdist := source_original_primitive_pair_lifts_distinct434
    Q c d hc hd hne
  exact hdist ((inv_mul_eq_one).mp hh)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitivePairPrimeValues -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- TRUE original pair-character quotient at its honest common
conductor: this is an equality of COMPLEX prime character
values, not a synthetically centered test. -/
theorem source_original_primitive_pair_common_eval434
    (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (p : ℕ) :
    sourceOriginalPrimitivePairQuotient434 Q c d
      (p : ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d)) =
    star ((DirichletCharacter.changeLevel
      (Nat.dvd_lcm_left (c.1.val+1) (d.1.val+1)) c.2)
        (p : ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))) *
      ((DirichletCharacter.changeLevel
      (Nat.dvd_lcm_right (c.1.val+1) (d.1.val+1)) d.2)
        (p : ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))) := by
  unfold sourceOriginalPrimitivePairQuotient434 sourceOriginalPrimitiveCommonLevel434
  rw [MulChar.mul_apply]
  rw [← MulChar.star_apply']

/-- Original admissible BIG primes p>Q² are AUTOMATICALLY
coprime to the honest common modulus lcm(qχ,qψ)≤Q². -/
theorem source_original_primitive_pair_big_prime_coprime434
    (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (p : ℕ) (hp : p.Prime) (hpBig : Q^2 < p) :
    IsCoprime (p:ℤ)
      (sourceOriginalPrimitiveCommonLevel434 Q c d:ℤ) := by
  have hMod := source_original_primitive_common_level_le_square434
    Q c d
  have hnot : ¬p ∣ sourceOriginalPrimitiveCommonLevel434 Q c d := by
    intro hdiv
    have hpositive : 0 <
        sourceOriginalPrimitiveCommonLevel434 Q c d := by
      unfold sourceOriginalPrimitiveCommonLevel434
      exact Nat.lcm_pos (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
    have hle := Nat.le_of_dvd hpositive hdiv
    omega
  exact (hp.coprime_iff_not_dvd.mpr hnot).isCoprime

/-- ACTUAL original primitive characters of different
possible levels combine to ONE nonprincipal Dirichlet
character at the common modulus, on every TRUE BIG prime
p exceeding Q². This is the exact prerequisite for the
source03 application of Siegel–Walfisz to its offdiagonal
character Gram; no character-sum saving is presumed. -/
theorem source_original_primitive_pair_prime_eval434
    (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (p : ℕ) (hp : p.Prime) (hpBig : Q^2 < p) :
    star (c.2 (p:ZMod (c.1.val+1))) *
      d.2 (p:ZMod (d.1.val+1)) =
    sourceOriginalPrimitivePairQuotient434 Q c d
      (p:ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d)) := by
  have hcop := source_original_primitive_pair_big_prime_coprime434
    Q c d p hp hpBig
  have hχ := DirichletCharacter.changeLevel_eq_cast_of_dvd'
    c.2 (Nat.dvd_lcm_left (c.1.val+1) (d.1.val+1)) hcop
  have hψ := DirichletCharacter.changeLevel_eq_cast_of_dvd'
    d.2 (Nat.dvd_lcm_right (c.1.val+1) (d.1.val+1)) hcop
  rw [source_original_primitive_pair_common_eval434]
  simp only [Int.cast_natCast] at hχ hψ
  unfold sourceOriginalPrimitiveCommonLevel434
  rw [hχ,hψ]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveGramQuotientSlice -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- A genuine one-prime source03 Gram slice between
TWO ACTUAL ORIGINAL primitive characters equals the
single-character harmonic sum for their NONPRINCIPAL
quotient at the true common modulus lcm(qχ,qψ)≤Q².
Every prime is an original BIG support prime > Q²,
and the GLOBAL product-cell constraint is retained
EXACTLY with the moving product R of other source labels. -/
theorem source_original_primitive_gram_local_quotient_slice434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ) (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (i : ι)
    (hBIG : ∀ p ∈ S i, p.Prime ∧ Q^2 < p)
    (r : (k : {k : ι // k ≠ i}) →
        {p : ℕ // p ∈ S k.val}) :
    sourceOriginalGramLocalPrimeSlice434 S mu h j
       (fun n => c.2 (n:ZMod (c.1.val+1)))
       (fun n => d.2 (n:ZMod (d.1.val+1))) i r =
    ∑ p : {p : ℕ // p ∈ S i},
       (mu i p.val : ℂ) *
       (if sourceOriginalLiteralLogCell434 h j
           (p.val * sourceOriginalGramOtherPrimeProduct434 S i r)
        then sourceOriginalPrimitivePairQuotient434 Q c d
           (p.val : ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))
        else 0) := by
  unfold sourceOriginalGramLocalPrimeSlice434
  apply Finset.sum_congr rfl
  intro p _
  obtain ⟨hp,hbig⟩ := hBIG p.val p.property
  have hχ := source_original_primitive_pair_prime_eval434
      Q c d p.val hp hbig
  by_cases hcell : sourceOriginalLiteralLogCell434 h j
     (p.val * sourceOriginalGramOtherPrimeProduct434 S i r)
  · simp only [if_pos hcell]
    rw [hχ]
  · simp only [if_neg hcell]

/-- Distinct source03 primitive characters reduce to one
genuine NONPRINCIPAL character of modulus at most Q²;
the log-product cell restricts its primes to an interval
after freezing the OTHER independent marked source primes.
This is the exact arithmetic point where an unconditional
Siegel–Walfisz sum bound is still needed. -/
theorem source_original_true_primitive_gram_reduction_nonprincipal434
    (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hc : c ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hd : d ∈ sourceOriginalActualPrimitiveCharacters434 Q)
    (hne : c ≠ d) :
    sourceOriginalPrimitivePairQuotient434 Q c d ≠ 1 ∧
    sourceOriginalPrimitiveCommonLevel434 Q c d ≤ Q^2 := by
  exact ⟨source_original_distinct_primitive_pair_quotient_nonprincipal434
     Q c d hc hd hne,
     source_original_primitive_common_level_le_square434 Q c d⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimeAbel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- EXACT original one-prime prefix sum for arbitrary complex
Dirichlet character weights on a numerical interval (a,n].
Values may be zero on composites or outside real source prime
intervals; no positivity or cancellation input is assumed. -/
noncomputable def sourceOriginalPrimePrefix434
    (a n : ℕ) (z : ℕ → ℂ) : ℂ :=
  ∑ k ∈ Finset.Ioc a n, z k

/-- DISCRETE COMPLEX ABEL SUMMATION in a form with no division
by zero and no truncated endpoint artifact:
Σ_{a<k≤N} z(k)/k = A(N)/(N+1)
       + Σ_{a<k≤N} A(k)*(1/k - 1/(k+1)).
This identity is valid for arbitrary characters or test
sequences z(k); it does NOT assume Siegel–Walfisz.
When z(k)=1_{prime∈source interval}ρ(k), this is EXACTLY
the 1/p harmonic weighted character sum in source03. -/
theorem source_original_prime_abel_exact434
    (a n : ℕ) (han : a ≤ n)
    (z : ℕ → ℂ) :
    (∑ k ∈ Finset.Ioc a n, z k / (k:ℂ)) =
    sourceOriginalPrimePrefix434 a n z /
      (((n+1:ℕ):ℂ)) +
    ∑ k ∈ Finset.Ioc a n,
       sourceOriginalPrimePrefix434 a k z *
         (1/(k:ℂ) - 1/(((k+1:ℕ):ℂ))) := by
  induction n, han using Nat.le_induction with
  | base =>
      simp [sourceOriginalPrimePrefix434]
  | succ n hna ih =>
      have hA : sourceOriginalPrimePrefix434 a (n+1) z =
          sourceOriginalPrimePrefix434 a n z + z (n+1) := by
        unfold sourceOriginalPrimePrefix434
        rw [Finset.sum_Ioc_succ_top hna]
      rw [Finset.sum_Ioc_succ_top hna
          (fun k => z k/(k:ℂ))]
      rw [Finset.sum_Ioc_succ_top hna
          (fun k => sourceOriginalPrimePrefix434 a k z *
             (1/(k:ℂ) - 1/(((k+1:ℕ):ℂ))))]
      rw [hA, ih]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimeAbelTelescoping -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The reciprocal-prime Abel telescoping kernel is literally
NONNEGATIVE at all actual positive prime indices k≥1. -/
theorem source_original_prime_abel_kernel_nonnegative434
    (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ (1/(k:ℝ) - 1/(((k+1:ℕ):ℝ))) := by
  have hpos : (0:ℝ) < k := by exact_mod_cast hk
  have hle : (k:ℝ) ≤ ((k+1:ℕ):ℝ) := by exact_mod_cast Nat.le_succ k
  exact sub_nonneg.mpr (one_div_le_one_div_of_le hpos hle)

/-- EXACT summation of positive reciprocal weighting increments
over ANY source BIG numerical interval (a,n]:
Σ_{k=a+1}^n (1/k -1/(k+1))=1/(a+1)-1/(n+1).
The lower cutoff is never zero, independent of a≥0. -/
theorem source_original_prime_abel_kernel_telescope434
    (a n : ℕ) (han : a ≤ n) :
    (∑ k ∈ Finset.Ioc a n,
       (1/(k:ℝ) - 1/(((k+1:ℕ):ℝ)))) =
    1/(((a+1:ℕ):ℝ)) - 1/(((n+1:ℕ):ℝ)) := by
  induction n, han using Nat.le_induction with
  | base =>
      simp
  | succ n hna ih =>
      rw [Finset.sum_Ioc_succ_top hna]
      rw [ih]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- The REAL version of the source exact Abel kernel equals
its COMPLEX weight; no synthetic positive/complex factor is
introduced when taking physical character sum norms. -/
theorem source_original_prime_abel_kernel_cast434
    (k : ℕ) :
    (1/(k:ℂ) - 1/(((k+1:ℕ):ℂ))) =
    ((1/(k:ℝ) - 1/(((k+1:ℕ):ℝ))) : ℂ) := by
  push_cast
  ring

/-- The TRUE complex Abel increment has real nonnegative norm,
exactly 1/(k(k+1)). No spurious factor 2 or abs loss enters
source03's harmonic-prime character partial summation. -/
theorem source_original_prime_abel_kernel_complex_norm434
    (k : ℕ) (hk : 1 ≤ k) :
    ‖1/(k:ℂ)-1/(((k+1:ℕ):ℂ))‖ =
    (1/(k:ℝ)-1/(((k+1:ℕ):ℝ))) := by
  have hkC : (k:ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk1C : (((k+1:ℕ):ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : k+1 ≠ 0)
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk1R : (((k+1:ℕ):ℝ)) ≠ 0 := by
    exact_mod_cast (by omega : k+1 ≠ 0)
  have hratC : 1/(k:ℂ) - 1/(((k+1:ℕ):ℂ)) =
      1/((k:ℂ)*(((k+1:ℕ):ℂ))) := by
    field_simp
    norm_num [Nat.cast_add]
  have hratR : 1/(k:ℝ) - 1/(((k+1:ℕ):ℝ)) =
      1/((k:ℝ)*(((k+1:ℕ):ℝ))) := by
    field_simp
    norm_num [Nat.cast_add]
  rw [hratC, hratR, norm_div]
  simp only [norm_one, norm_mul, norm_natCast, one_div]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimeAbelBound -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- EXACT quantitative source03 analytic transition from
a UNIFORM arithmetic prime-character prefix bound to the
true reciprocal-prime harmonic sum on the interval (a,n].
No false assertion that a nonprincipal character has
exactly zero finite source-prime average.
The decay is B/(a+1), with NO group-size loss. -/
theorem source_original_prime_harmonic_from_prefix434
    (a n : ℕ) (han : a ≤ n) (z : ℕ → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hPrefix : ∀ k ∈ Finset.Icc a n,
      ‖sourceOriginalPrimePrefix434 a k z‖ ≤ B) :
    ‖∑ k ∈ Finset.Ioc a n, z k / (k:ℂ)‖ ≤
      B / (((a+1:ℕ):ℝ)) := by
  let A (k : ℕ) : ℂ := sourceOriginalPrimePrefix434 a k z
  let δ (k : ℕ) : ℝ :=
    (1/(k:ℝ) - 1/(((k+1:ℕ):ℝ)))
  have hA (k : ℕ) (hk : k ∈ Finset.Icc a n) :
      ‖A k‖ ≤ B := hPrefix k hk
  have hn : ‖A n / (((n+1:ℕ):ℂ))‖ ≤
      B / (((n+1:ℕ):ℝ)) := by
    rw [norm_div]
    simp only [norm_natCast]
    have hp : 0 ≤ (((n+1:ℕ):ℝ))⁻¹ := by positivity
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (hA n (Finset.mem_Icc.mpr ⟨han,le_rfl⟩)) hp
  have hδ (k : ℕ) (hk : k ∈ Finset.Ioc a n) : 0 ≤ δ k := by
    exact source_original_prime_abel_kernel_nonnegative434 k
      (by
        have hlt : a < k := (Finset.mem_Ioc.mp hk).1
        omega)
  have hterm (k : ℕ) (hk : k ∈ Finset.Ioc a n) :
      ‖A k * (1/(k:ℂ) - 1/(((k+1:ℕ):ℂ)))‖ ≤
       B * δ k := by
    rw [norm_mul]
    have hcast : ‖1/(k:ℂ)-1/(((k+1:ℕ):ℂ))‖ = δ k := by
      exact source_original_prime_abel_kernel_complex_norm434 k (by
        have hlt : a < k := (Finset.mem_Ioc.mp hk).1
        omega)
    rw [hcast]
    exact mul_le_mul_of_nonneg_right
      (hA k (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Ioc.mp hk).1.le,(Finset.mem_Ioc.mp hk).2⟩))
      (hδ k hk)
  rw [source_original_prime_abel_exact434 a n han z]
  calc
    ‖A n / (((n+1:ℕ):ℂ)) +
      ∑ k ∈ Finset.Ioc a n,
        A k * (1/(k:ℂ)-1/(((k+1:ℕ):ℂ)))‖ ≤
      ‖A n / (((n+1:ℕ):ℂ))‖ +
      ‖∑ k ∈ Finset.Ioc a n,
        A k*(1/(k:ℂ)-1/(((k+1:ℕ):ℂ)))‖ :=
        norm_add_le _ _
    _ ≤ ‖A n / (((n+1:ℕ):ℂ))‖ +
      ∑ k ∈ Finset.Ioc a n,
        ‖A k * (1/(k:ℂ)-1/(((k+1:ℕ):ℂ)))‖ :=
      add_le_add_right (norm_sum_le _ _) _
    _ ≤ B / (((n+1:ℕ):ℝ)) +
      ∑ k ∈ Finset.Ioc a n, B * δ k := by
      apply add_le_add hn
      exact Finset.sum_le_sum hterm
    _ = B / (((a+1:ℕ):ℝ)) := by
      rw [← Finset.mul_sum]
      rw [source_original_prime_abel_kernel_telescope434 a n han]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimeCellAbelSupport -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The source's ORIGINAL global log-product cell can be
restricted to its true selected prime interval (a,n].
No enlargement of the original finite prime support.
The cover assumption is a literal arithmetic interval
containment to be discharged from true log geometry. -/
theorem source_original_finite_cell_interval_cover434
    (P : Finset ℕ) (cell : ℕ → Prop) [DecidablePred cell]
    (a n : ℕ) (χ : ℕ → ℂ)
    (hcover : ∀ p ∈ P, cell p → p ∈ Finset.Ioc a n) :
    (∑ p ∈ P, if cell p then χ p / (p:ℂ) else 0) =
    (∑ k ∈ Finset.Ioc a n,
       (if k ∈ P ∧ cell k then χ k else 0) / (k:ℂ)) := by
  classical
  have hsets :
      P.filter cell =
      (Finset.Ioc a n).filter (fun k => k ∈ P ∧ cell k) := by
    ext k
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hP,hcell⟩
      exact ⟨hcover k hP hcell,hP,hcell⟩
    · rintro ⟨hk,hP,hcell⟩
      exact ⟨hP,hcell⟩
  calc
    _ = ∑ p ∈ P.filter cell, χ p / (p:ℂ) := by
      rw [Finset.sum_filter]
    _ = ∑ k ∈ (Finset.Ioc a n).filter
          (fun k => k∈P ∧ cell k), χ k / (k:ℂ) := by
        rw [← hsets]
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hc : k∈P ∧ cell k
      · simp [hc]
      · simp [hc]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimeCellAbelBound -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Exact arithmetic numerator for partial summation of the
TRUE finite source BIG prime support and GLOBAL product cell.
The factor k removes the original 1/k harmonic weight,
so actual Dirichlet-character prime-prefix bounds apply. -/
noncomputable def sourceOriginalWeightedCellPrimeNumerator434
    (P : Finset ℕ) (mu : ℕ → ℝ)
    (cell : ℕ → Prop) (χ : ℕ → ℂ) (k : ℕ) : ℂ :=
  if k ∈ P ∧ cell k then
    ((mu k : ℝ):ℂ) * (k:ℂ) * χ k else 0

/-- ACTUAL finite arithmetic partial summation:
a uniform bound on the TRUE moving prime-cell prefix
(with the exact physical source prime support P and weights μ)
controls its ORIGINAL harmonic character sum by B/(a+1).
No synthetic zero-mean assumption and no enlargement of
the global product logarithmic cell. -/
theorem source_original_weighted_global_cell_prime_abel434
    (P : Finset ℕ) (mu : ℕ → ℝ)
    (cell : ℕ → Prop) (χ : ℕ → ℂ)
    (a n : ℕ) (han : a ≤ n)
    (hpos : ∀ p ∈ P, 0 < p)
    (hcover : ∀ p ∈ P, cell p → p ∈ Finset.Ioc a n)
    (B : ℝ) (hB : 0 ≤ B)
    (hPrefix : ∀ k ∈ Finset.Icc a n,
       ‖sourceOriginalPrimePrefix434 a k
           (sourceOriginalWeightedCellPrimeNumerator434 P mu cell χ)‖
         ≤ B) :
    ‖∑ p ∈ P, (mu p:ℂ) *
       (if cell p then χ p else 0)‖ ≤
      B / (((a+1:ℕ):ℝ)) := by
  classical
  let z := sourceOriginalWeightedCellPrimeNumerator434 P mu cell χ
  have hcell (p : ℕ) (hp : p ∈ P) :
      (mu p:ℂ) * (if cell p then χ p else 0) =
      (if cell p then ((mu p:ℂ)*(p:ℂ))*χ p/(p:ℂ)
       else 0) := by
    by_cases hc : cell p
    · have hpne : (p:ℂ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (hpos p hp))
      simp only [if_pos hc]
      field_simp
    · simp [hc]
  have hsum :
      (∑ p ∈ P, (mu p:ℂ) *
         (if cell p then χ p else 0)) =
      ∑ k ∈ Finset.Ioc a n, z k / (k:ℂ) := by
    calc
      _ = ∑ p ∈ P, (if cell p then
          ((mu p:ℂ)*(p:ℂ))*χ p/(p:ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hcell p hp
      _ = ∑ k ∈ Finset.Ioc a n,
         (if k∈P ∧ cell k
          then ((mu k:ℂ)*(k:ℂ))*χ k else 0)/(k:ℂ) :=
        source_original_finite_cell_interval_cover434
          P cell a n (fun k => ((mu k:ℂ)*(k:ℂ))*χ k) hcover
      _ = _ := by rfl
  rw [hsum]
  exact source_original_prime_harmonic_from_prefix434
    a n han z B hB hPrefix
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveGramAbelBridge -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- For the actual original source03 two-primitive-character
Gram slice, all its true BIG primes exceed the joint modulus
Q², its GLOBAL cell remains the moving product pR, and
an ordinary weighted nonprincipal CHARACTER PREFIX bound
controls its exact harmonic offdiagonal entry through Abel.
This is a sharp arithmetic interface, not an assumed small
Gram frame or an assertion that SW has been formalized. -/
theorem source_original_primitive_gram_local_from_prefix434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ) (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (i : ι) (hBIG : ∀ p ∈ S i, p.Prime ∧ Q^2 < p)
    (r : (k : {k : ι // k ≠ i}) →
      {p : ℕ // p ∈ S k.val})
    (a n : ℕ) (han : a ≤ n)
    (hcover : ∀ p ∈ S i,
      sourceOriginalLiteralLogCell434 h j
        (p * sourceOriginalGramOtherPrimeProduct434 S i r) →
        p ∈ Finset.Ioc a n)
    (B : ℝ) (hB : 0 ≤ B)
    (hPrefix : ∀ k ∈ Finset.Icc a n,
      ‖sourceOriginalPrimePrefix434 a k
        (sourceOriginalWeightedCellPrimeNumerator434 (S i)
          (mu i)
          (fun p => sourceOriginalLiteralLogCell434 h j
            (p * sourceOriginalGramOtherPrimeProduct434 S i r))
          (fun p => sourceOriginalPrimitivePairQuotient434 Q c d
            (p:ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))))‖
          ≤ B) :
    ‖sourceOriginalGramLocalPrimeSlice434 S mu h j
       (fun p => c.2 (p:ZMod (c.1.val+1)))
       (fun p => d.2 (p:ZMod (d.1.val+1))) i r‖ ≤
    B / (((a+1:ℕ):ℝ)) := by
  classical
  rw [source_original_primitive_gram_local_quotient_slice434
    S mu h j Q c d i hBIG r]
  let R := sourceOriginalGramOtherPrimeProduct434 S i r
  let χ : ℕ → ℂ :=
    fun p => sourceOriginalPrimitivePairQuotient434 Q c d
      (p:ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))
  let cell : ℕ → Prop :=
    fun p => sourceOriginalLiteralLogCell434 h j (p*R)
  have hattach :
    (∑ p : {p : ℕ // p ∈ S i},
      (mu i p.val:ℂ) * (if cell p.val then χ p.val else 0)) =
    ∑ k ∈ S i, (mu i k:ℂ) *
      (if cell k then χ k else 0) := by
    simpa only [Finset.univ_eq_attach] using
      (Finset.sum_attach (S i)
        (fun p : ℕ =>
          (mu i p:ℂ)*(if cell p then χ p else 0)))
  change ‖∑ p : {p : ℕ // p ∈ S i},
    (mu i p.val:ℂ)*(if cell p.val then χ p.val else 0)‖ ≤ _
  rw [hattach]
  exact source_original_weighted_global_cell_prime_abel434
    (S i) (mu i) cell χ a n han
    (fun p hp => (hBIG p hp).1.pos) hcover B hB hPrefix
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualPrimitiveDiagonal -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Real original source03 global product-cell mass under the
unchanged finite harmonic prime law. This is the TRUE diagonal
normalizer in the primitive-character frame, not an assumed ν_j. -/
noncomputable def sourceOriginalRealGramCellMass434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ) : ℝ :=
  ∑ a : SourceOriginalGramPrimeTuple434 S,
    if sourceOriginalLiteralLogCell434 h j
      (sourceOriginalGramPrimeProduct434 S a)
    then sourceOriginalGramPrimeMass434 S mu a else 0

/-- On the actual BIG prime support, every prime p>Q² is
coprime to the literal level qχ≤Q of a primitive character.
Thus all actual labeled prime marks are invertible modulo qχ. -/
theorem source_original_primitive_big_prime_unit434
    (Q : ℕ)
    (c : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (p : ℕ) (hp : p.Prime) (hpBIG : Q^2 < p) :
    IsUnit (p : ZMod (c.1.val+1)) := by
  have hQ : 1 ≤ Q := by
    have hc : c.1.val < Q := c.1.isLt
    omega
  have hQ2 : Q ≤ Q^2 := by
    calc
      Q = Q*1 := by omega
      _ ≤ Q*Q := Nat.mul_le_mul_left Q hQ
      _ = Q^2 := by ring
  have hq : c.1.val+1 ≤ Q := by omega
  have hnot : ¬p ∣ c.1.val+1 := by
    intro hdiv
    have hle := Nat.le_of_dvd (Nat.zero_lt_succ _) hdiv
    omega
  exact (ZMod.isUnit_iff_coprime p (c.1.val+1)).mpr
    (hp.coprime_iff_not_dvd.mpr hnot)

/-- ALL original labeled BIG primes are units for each actual
source primitive character, even when numerical primes repeat. -/
theorem source_original_primitive_actual_product_unit434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (Q : ℕ)
    (c : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hBIG : ∀ i p, p ∈ S i → p.Prime ∧ Q^2 < p)
    (a : SourceOriginalGramPrimeTuple434 S) :
    IsUnit ((sourceOriginalGramPrimeProduct434 S a : ℕ) :
      ZMod (c.1.val+1)) := by
  unfold sourceOriginalGramPrimeProduct434
  rw [Nat.cast_prod]
  apply IsUnit.prod_univ_iff.mpr
  intro i
  exact source_original_primitive_big_prime_unit434
    Q c (a i).val (hBIG i (a i).val (a i).property).1
      (hBIG i (a i).val (a i).property).2

/-- Exact unit modulus of each ACTUAL primitive character
on the true source BIG product, no independent prime proxy. -/
theorem source_original_primitive_actual_product_norm_one434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (Q : ℕ)
    (c : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hBIG : ∀ i p, p ∈ S i → p.Prime ∧ Q^2 < p)
    (a : SourceOriginalGramPrimeTuple434 S) :
    ‖c.2 ((sourceOriginalGramPrimeProduct434 S a : ℕ) :
        ZMod (c.1.val+1))‖ = 1 := by
  let D := (sourceOriginalGramPrimeProduct434 S a : ℕ)
  have hu : IsUnit (D : ZMod (c.1.val+1)) :=
    source_original_primitive_actual_product_unit434
      S Q c hBIG a
  simpa only [IsUnit.unit_spec] using
    (c.2.unit_norm_eq_one hu.unit)

/-- The DIAGONAL of the TRUE original primitive-character
GLOBAL log-cell Gram is exactly the real physical probability
mass of that SAME global product cell. Distinct numeric prime
labels and original finite normalized reciprocal weights
are left unchanged. No asymptotic prime-distribution assumption. -/
theorem source_original_actual_primitive_gram_diagonal434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ) (Q : ℕ)
    (c : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (hBIG : ∀ i p, p ∈ S i → p.Prime ∧ Q^2 < p) :
    sourceOriginalActualPrimitiveGramEntry434 S mu h j Q c c =
      (sourceOriginalRealGramCellMass434 S mu h j : ℂ) := by
  unfold sourceOriginalActualPrimitiveGramEntry434
    sourceOriginalGramCellEntry434
    sourceOriginalRealGramCellMass434
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hcell : sourceOriginalLiteralLogCell434 h j
    (sourceOriginalGramPrimeProduct434 S a)
  · simp only [if_pos hcell, Complex.ofReal_mul]
    have hn := source_original_primitive_actual_product_norm_one434
      S Q c hBIG a
    have hchar :
        star (c.2 ((sourceOriginalGramPrimeProduct434 S a:ℕ):
           ZMod (c.1.val+1))) *
           c.2 ((sourceOriginalGramPrimeProduct434 S a:ℕ):
           ZMod (c.1.val+1)) = 1 := by
      have hz := Complex.normSq_eq_conj_mul_self
         (z := c.2 ((sourceOriginalGramPrimeProduct434 S a:ℕ):
           ZMod (c.1.val+1)))
      rw [Complex.normSq_eq_norm_sq, hn] at hz
      simpa only [Complex.star_def, one_pow, Complex.ofReal_one] using hz.symm
    rw [hchar, mul_one]
  · simp only [if_neg hcell]
    simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeBigGroupedPrimeEquiv -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Original SOURCE03 marked position (g,i) has EXACTLY
the same BIG group g after passing through the genuine
per-group finite enumeration; no other BIG or SMALL group
is inserted by the grouped C6 indexing. -/
theorem source_original_probe_group_sigma_group434
    {G : Type} [DecidableEq G] (m : ℕ)
    (block : Finset G) (A : Finset (G × Fin m))
    (hBlock : A ⊆ sourceOriginalProbeBlock434 block m)
    (z : Σ g : block,
        Fin (sourceOriginalProbeChosenGroupCount434 m A g.val)) :
    (sourceOriginalProbeGroupSigmaEquiv434 m block A hBlock z).val.1 =
       z.1.val := by
  rfl

/-- The exact marked BIG prime tuples indexed by the SOURCE03
A- or B-pattern subset are equivalent to the grouped C6
prime tuples with slot multiplicity equal to each group's
ACTUAL number of freed probes. The coordinate support
S(g) is not replaced or enlarged and numerical repetitions
in separate marked slots are fully retained. -/
noncomputable def sourceOriginalProbeBigGroupedPrimeEquiv434
    {G : Type} [DecidableEq G] (m : ℕ)
    (block : Finset G) (A : Finset (G × Fin m))
    (hBlock : A ⊆ sourceOriginalProbeBlock434 block m)
    (S : G → Finset ℕ) :
    SourceOriginalGramPrimeTuple434
      (fun z : Σ g : block,
        Fin (sourceOriginalProbeChosenGroupCount434 m A g.val) =>
          S z.1.val) ≃
    SourceOriginalGramPrimeTuple434
      (fun z : A => S z.val.1) := by
  let E := sourceOriginalProbeGroupSigmaEquiv434 m block A hBlock
  let B : A → Type := fun z => {p : ℕ // p ∈ S z.val.1}
  have hSupport (z : Σ g : block,
      Fin (sourceOriginalProbeChosenGroupCount434 m A g.val)) :
      B (E z) = {p : ℕ // p ∈ S z.1.val} := by
    rfl
  exact Equiv.piCongrLeft B E

/-- SOURCE03 grouped prime coordinates and original marked
slot coordinates agree pointwise after the reindexing.
This is the pointwise prerequisite for preserving both
arithmetic products and harmonic weights, not a postulated
identity of the final signed operator. -/
theorem source_original_probe_big_grouped_prime_equiv_apply434
    {G : Type} [DecidableEq G] (m : ℕ)
    (block : Finset G) (A : Finset (G × Fin m))
    (hBlock : A ⊆ sourceOriginalProbeBlock434 block m)
    (S : G → Finset ℕ)
    (x : SourceOriginalGramPrimeTuple434
      (fun z : Σ g : block,
        Fin (sourceOriginalProbeChosenGroupCount434 m A g.val) =>
          S z.1.val))
    (z : Σ g : block,
      Fin (sourceOriginalProbeChosenGroupCount434 m A g.val)) :
    (sourceOriginalProbeBigGroupedPrimeEquiv434 m block A hBlock S x
      (sourceOriginalProbeGroupSigmaEquiv434 m block A hBlock z)).val =
      (x z).val := by
  exact congrArg Subtype.val
    (Equiv.piCongrLeft_apply_apply
      (fun z : A => {p : ℕ // p ∈ S z.val.1})
      (sourceOriginalProbeGroupSigmaEquiv434 m block A hBlock)
      x z)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualPrimitiveGramMagnitude -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- TRUE original source BIG harmonic marked-tuple probability
is nonnegative, with no independence approximation. -/
theorem source_original_gram_full_prime_mass_nonneg434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (a : SourceOriginalGramPrimeTuple434 S) :
    0 ≤ sourceOriginalGramPrimeMass434 S mu a := by
  unfold sourceOriginalGramPrimeMass434
  apply Finset.prod_nonneg
  intro i _
  exact hmu i (a i).val (a i).property

/-- For ACTUAL source03 BIG primes strictly above Q² and
arbitrary original finite nonnegative prime weights, the
offdiagonal primitive-character global-cell Gram entry has
modulus ≤ its EXACT diagonal probability mass ν_j.
This is a genuine unconditional bound, no SW, no character
orthogonality or conjectural mixing assumption. -/
theorem source_original_actual_primitive_gram_norm_le_mass434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (h : ℝ) (j : ℤ) (Q : ℕ)
    (hBIG : ∀ i p, p ∈ S i → p.Prime ∧ Q^2 < p)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)) :
    ‖sourceOriginalActualPrimitiveGramEntry434 S mu h j Q c d‖ ≤
       sourceOriginalRealGramCellMass434 S mu h j := by
  unfold sourceOriginalActualPrimitiveGramEntry434
    sourceOriginalGramCellEntry434
  have hterm (a : SourceOriginalGramPrimeTuple434 S) :
      ‖((sourceOriginalGramPrimeMass434 S mu a : ℝ):ℂ) *
        (if sourceOriginalLiteralLogCell434 h j
             (sourceOriginalGramPrimeProduct434 S a)
         then star (c.2 ((sourceOriginalGramPrimeProduct434 S a:ℕ):
             ZMod (c.1.val+1))) *
           d.2 ((sourceOriginalGramPrimeProduct434 S a:ℕ):
             ZMod (d.1.val+1))
         else 0)‖ =
      if sourceOriginalLiteralLogCell434 h j
          (sourceOriginalGramPrimeProduct434 S a)
      then sourceOriginalGramPrimeMass434 S mu a else 0 := by
    have hw := source_original_gram_full_prime_mass_nonneg434
      S mu hmu a
    by_cases hc : sourceOriginalLiteralLogCell434 h j
      (sourceOriginalGramPrimeProduct434 S a)
    · have hc1 := source_original_primitive_actual_product_norm_one434
        S Q c hBIG a
      have hd1 := source_original_primitive_actual_product_norm_one434
        S Q d hBIG a
      simp only [if_pos hc, norm_mul, norm_star,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw,
        hc1,hd1, mul_one]
    · simp only [if_neg hc, mul_zero, norm_zero]
  calc
    _ ≤ ∑ a : SourceOriginalGramPrimeTuple434 S,
        ‖((sourceOriginalGramPrimeMass434 S mu a:ℝ):ℂ) *
         (if sourceOriginalLiteralLogCell434 h j
           (sourceOriginalGramPrimeProduct434 S a)
          then star (c.2 ((sourceOriginalGramPrimeProduct434 S a:ℕ):
            ZMod (c.1.val+1))) *
            d.2 ((sourceOriginalGramPrimeProduct434 S a:ℕ):
            ZMod (d.1.val+1))
          else 0)‖ := norm_sum_le _ _
    _ = sourceOriginalRealGramCellMass434 S mu h j := by
      unfold sourceOriginalRealGramCellMass434
      apply Finset.sum_congr rfl
      intro a _
      exact hterm a
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualPrimitiveGramCellProbability -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The FULL original independently indexed BIG prime
tuple distribution (possibly different finite prime sets at
different indices) is exactly normalized, not uniform. -/
theorem source_original_gram_full_prime_law_one434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i, ∑ p ∈ S i, mu i p = 1) :
    (∑ a : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeMass434 S mu a) = 1 := by
  have hrow (i : ι) :
      (∑ p : {p : ℕ // p ∈ S i}, mu i p.val) = 1 := by
    simpa using (Finset.sum_attach (S i)
      (fun p : ℕ => mu i p)).trans (hmu i)
  unfold sourceOriginalGramPrimeMass434
  calc
    (∑ a : SourceOriginalGramPrimeTuple434 S,
      ∏ i : ι, mu i (a i).val) =
      ∏ i : ι, ∑ p : {p : ℕ // p ∈ S i}, mu i p.val :=
      (Fintype.prod_sum
        (fun (i : ι) (p : {p : ℕ // p ∈ S i}) =>
          mu i p.val)).symm
    _ = 1 := by simp only [hrow, Finset.prod_const_one]

/-- The exact source03 global half-open logarithmic-cell
probability is BETWEEN ZERO AND ONE. Its diagonal
character Gram mass is never an independently prescribed
cell normalizer or artificially chosen probability. -/
theorem source_original_real_gram_cell_probability434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i, ∑ p ∈ S i, mu i p = 1)
    (hmuPos : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (h : ℝ) (j : ℤ) :
    0 ≤ sourceOriginalRealGramCellMass434 S mu h j ∧
    sourceOriginalRealGramCellMass434 S mu h j ≤ 1 := by
  have hw (a : SourceOriginalGramPrimeTuple434 S) :
      0 ≤ sourceOriginalGramPrimeMass434 S mu a :=
    source_original_gram_full_prime_mass_nonneg434 S mu hmuPos a
  have hpos :
      0 ≤ sourceOriginalRealGramCellMass434 S mu h j := by
    unfold sourceOriginalRealGramCellMass434
    apply Finset.sum_nonneg
    intro a _
    by_cases hc : sourceOriginalLiteralLogCell434 h j
      (sourceOriginalGramPrimeProduct434 S a)
    · simpa only [if_pos hc] using hw a
    · simp [hc]
  have hcell :
      sourceOriginalRealGramCellMass434 S mu h j ≤
      ∑ a : SourceOriginalGramPrimeTuple434 S,
        sourceOriginalGramPrimeMass434 S mu a := by
    unfold sourceOriginalRealGramCellMass434
    apply Finset.sum_le_sum
    intro a _
    by_cases hc : sourceOriginalLiteralLogCell434 h j
      (sourceOriginalGramPrimeProduct434 S a)
    · simp [hc]
    · simp [hc, hw a]
  exact ⟨hpos, hcell.trans
     (le_of_eq (source_original_gram_full_prime_law_one434
       S mu hmu))⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalDiscardedCellMass -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The true SOURCE03 labelled-prime physical type has the SAME
discarded GLOBAL log-product mass as its original piFinset
formulation. This transports the unconditional C134 estimate
to the actual source03 physical Gram/kernel state type, where
it can combine with the verified independent two-ENDPOINT rare
event L² saving C138. No replacement of prime laws or
assumed identical prime supports. -/
theorem source_original_physical_discarded_global_mass434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h xi : ℝ) (hh : 0 < h) (hxi : 0 < xi) :
    (∑ a : SourceOriginalGramPrimeTuple434 S,
      if sourceOriginalLiteralLogCellIndex434 h
           (sourceOriginalGramPrimeProduct434 S a) ∈
           sourceOriginalFiniteActiveLogCells434 S mu h xi
      then 0 else sourceOriginalGramPrimeMass434 S mu a) ≤
      ((sourceOriginalCandidateLogCells434 S h).card:ℝ)*xi := by
  classical
  let states := Fintype.piFinset S
  let e := sourceFiniteListFamilyEquiv434 S
  let F : (ι → ℕ) → ℝ := fun a =>
    if sourceOriginalLiteralLogCellIndex434 h (∏ i : ι, a i) ∈
      sourceOriginalFiniteActiveLogCells434 S mu h xi
    then 0 else sourceSharedLaw434 mu a
  let G : SourceOriginalGramPrimeTuple434 S → ℝ := fun a =>
    if sourceOriginalLiteralLogCellIndex434 h
      (sourceOriginalGramPrimeProduct434 S a) ∈
      sourceOriginalFiniteActiveLogCells434 S mu h xi
    then 0 else sourceOriginalGramPrimeMass434 S mu a
  have hpoint (a : ↑states) : F a.val = G (e a) := by
    rfl
  have hReindex : (∑ a ∈ states, F a) =
      ∑ b : SourceOriginalGramPrimeTuple434 S, G b := by
    calc
      _ = ∑ a : ↑states, F a.val :=
        (Finset.sum_coe_sort states F).symm
      _ = ∑ b : SourceOriginalGramPrimeTuple434 S, G b :=
        Fintype.sum_equiv e
          (fun a : ↑states => F a.val) G hpoint
  have hOrig := source_original_true_discarded_cell_mass434
    S mu h xi hh hxi
  change (∑ a ∈ states, F a) ≤ _ at hOrig
  change (∑ b : SourceOriginalGramPrimeTuple434 S, G b) ≤ _
  exact hReindex.symm ▸ hOrig
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHarmonicSelectedDiscarded -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The selected physical source03 harmonic prime law in
the genuine dependent prime-label subtype spaces uses exactly
the SAME 1/(p*V_i) probability weights as the original
candidate/active GLOBAL log-cell law. Consequently, the real
probability of an unretained selected log-product cell is at
most its actual finite candidate-cell count times xi.
This bridges the two notational conventions 1/p/V and
1/(p*V), with no new assumption of equality of distributions. -/
theorem source_original_harmonic_selected_discarded_mass434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (V : ι → ℝ)
    (h xi : ℝ) (hh : 0 < h) (hxi : 0 < xi) :
    let mu : (i : ι) → {p : ℕ // p ∈ S i} → ℝ :=
      fun i p => sourceOriginalHarmonicPrimeMu434
        (fun p : {p : ℕ // p ∈ S i} => p.val) (V i) p
    let mu0 : ι → ℕ → ℝ := fun i p =>
      sourcePrimeSharedAtom434 (V i) p
    let active := sourceOriginalFiniteActiveLogCells434 S mu0 h xi
    (∑ a : SourceOriginalGramPrimeTuple434 S,
       (∏ i : ι, mu i (a i)) *
       (if sourceOriginalLiteralLogCellIndex434 h
            (sourceOriginalGramPrimeProduct434 S a) ∈ active
        then 0 else 1)) ≤
    ((sourceOriginalCandidateLogCells434 S h).card:ℝ)*xi := by
  classical
  let mu : (i : ι) → {p : ℕ // p ∈ S i} → ℝ :=
    fun i p => sourceOriginalHarmonicPrimeMu434
      (fun p : {p : ℕ // p ∈ S i} => p.val) (V i) p
  let mu0 : ι → ℕ → ℝ := fun i p =>
    sourcePrimeSharedAtom434 (V i) p
  let active := sourceOriginalFiniteActiveLogCells434 S mu0 h xi
  have hPoint (i : ι) (p : {p : ℕ // p ∈ S i}) :
      mu i p = mu0 i p.val := by
    dsimp [mu,mu0,sourceOriginalHarmonicPrimeMu434,
      sourcePrimeSharedAtom434]
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  have hMass (a : SourceOriginalGramPrimeTuple434 S) :
      (∏ i : ι, mu i (a i)) =
        sourceOriginalGramPrimeMass434 S mu0 a := by
    unfold sourceOriginalGramPrimeMass434
    apply Finset.prod_congr rfl
    intro i hi
    exact hPoint i (a i)
  have hRaw :=
    source_original_physical_discarded_global_mass434
      S mu0 h xi hh hxi
  change
    (∑ a : SourceOriginalGramPrimeTuple434 S,
       (∏ i : ι, mu i (a i)) *
       (if sourceOriginalLiteralLogCellIndex434 h
            (sourceOriginalGramPrimeProduct434 S a) ∈ active
        then 0 else 1)) ≤
      ((sourceOriginalCandidateLogCells434 S h).card:ℝ)*xi
  calc
    _ = (∑ a : SourceOriginalGramPrimeTuple434 S,
        if sourceOriginalLiteralLogCellIndex434 h
             (sourceOriginalGramPrimeProduct434 S a) ∈ active
        then 0 else sourceOriginalGramPrimeMass434 S mu0 a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hMass a]
      by_cases hc : sourceOriginalLiteralLogCellIndex434 h
          (sourceOriginalGramPrimeProduct434 S a) ∈ active
      · simp [hc]
      · simp [hc]
    _ ≤ ((sourceOriginalCandidateLogCells434 S h).card:ℝ)*xi := by
      exact hRaw
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalDiscardedTwoGlobalL2 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Exact normalization of the true product harmonic law on
ORIGINAL labelled prime subtype tuples. This is the same
law as the original independent finite piFinset source
model, via the genuine coordinate equivalence. -/
theorem source_original_physical_gram_prime_mass_total434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i, ∑ p ∈ S i, mu i p = 1) :
    (∑ a : SourceOriginalGramPrimeTuple434 S,
       sourceOriginalGramPrimeMass434 S mu a) = 1 := by
  classical
  let e := sourceFiniteListFamilyEquiv434 S
  have hmain := source_shared_law_total434 S mu hmu
  calc
    _ = ∑ a : ↑(Fintype.piFinset S),
        sourceSharedLaw434 mu a.val := by
      symm
      exact Fintype.sum_equiv e
        (fun a : ↑(Fintype.piFinset S) =>
          sourceSharedLaw434 mu a.val)
        (fun b : SourceOriginalGramPrimeTuple434 S =>
          sourceOriginalGramPrimeMass434 S mu b)
        (fun a => rfl)
    _ = ∑ a ∈ Fintype.piFinset S,
         sourceSharedLaw434 mu a := by
      exact Finset.sum_coe_sort _ _
    _ = 1 := hmain

/-- Genuine nonnegative physical prime tuple mass under
the unchanged coordinate-dependent source law. -/
theorem source_original_physical_gram_prime_mass_nonneg434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (a : SourceOriginalGramPrimeTuple434 S) :
    0 ≤ sourceOriginalGramPrimeMass434 S mu a := by
  unfold sourceOriginalGramPrimeMass434
  apply Finset.prod_nonneg
  intro i hi
  exact hmu i (a i).val (a i).property
 
/-- TRUE physical source03 TWO GLOBAL prime-label blocks:
the raw unit-amplitude major/minor phase on states with
a discarded A-cell OR a discarded B-cell has square
bilinear weighted-L² cost <=
2*(N_A+N_B)*xi * E_A(f)*E_B(g), where the candidate counts
are the ACTUAL attainable log-product cells in their true
different prime-support spaces (including repetitions).
No arbitrary supnorm assumption on f,g, no fake
uniform prime law or unjustified L² rare-event operator.
The coefficient bounds here are explicit geometric tasks:
the next step must show N_A,N_B = polynomial in L. -/
theorem source_original_physical_two_global_discarded_L2_bound434
    {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (hmuA : ∀ i, ∑ p ∈ SA i, muA i p = 1)
    (hmuNonnegA : ∀ i p, p ∈ SA i → 0 ≤ muA i p)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (hmuB : ∀ i, ∑ p ∈ SB i, muB i p = 1)
    (hmuNonnegB : ∀ i p, p ∈ SB i → 0 ≤ muB i p)
    (hA hB xi : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (hxi : 0 < xi)
    (f : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (g : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (H : SourceOriginalGramPrimeTuple434 SA ×
         SourceOriginalGramPrimeTuple434 SB → ℂ)
    (hH : ∀ q, ‖H q‖ ≤ 1) :
    let cA := sourceOriginalCandidateLogCells434 SA hA
    let cB := sourceOriginalCandidateLogCells434 SB hB
    let activeA := sourceOriginalFiniteActiveLogCells434 SA muA hA xi
    let activeB := sourceOriginalFiniteActiveLogCells434 SB muB hB xi
    ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
                SourceOriginalGramPrimeTuple434 SB,
      ((sourceOriginalGramPrimeMass434 SA muA q.1 *
          sourceOriginalGramPrimeMass434 SB muB q.2:ℝ):ℂ) *
        star (f q.1) * g q.2 *
        (if (sourceOriginalLiteralLogCellIndex434 hA
                (sourceOriginalGramPrimeProduct434 SA q.1) ∉ activeA) ∨
              (sourceOriginalLiteralLogCellIndex434 hB
                (sourceOriginalGramPrimeProduct434 SB q.2) ∉ activeB)
         then H q else 0))‖^2 ≤
     2*(((cA.card:ℝ)+(cB.card:ℝ))*xi) *
       (∑ a : SourceOriginalGramPrimeTuple434 SA,
         sourceOriginalGramPrimeMass434 SA muA a * ‖f a‖^2) *
       (∑ b : SourceOriginalGramPrimeTuple434 SB,
         sourceOriginalGramPrimeMass434 SB muB b * ‖g b‖^2) := by
  classical
  let XA := SourceOriginalGramPrimeTuple434 SA
  let XB := SourceOriginalGramPrimeTuple434 SB
  let wA : XA → ℝ := sourceOriginalGramPrimeMass434 SA muA
  let wB : XB → ℝ := sourceOriginalGramPrimeMass434 SB muB
  let activeA := sourceOriginalFiniteActiveLogCells434 SA muA hA xi
  let activeB := sourceOriginalFiniteActiveLogCells434 SB muB hB xi
  let cA := sourceOriginalCandidateLogCells434 SA hA
  let cB := sourceOriginalCandidateLogCells434 SB hB
  let badA : XA → Prop := fun a =>
    sourceOriginalLiteralLogCellIndex434 hA
      (sourceOriginalGramPrimeProduct434 SA a) ∉ activeA
  let badB : XB → Prop := fun b =>
    sourceOriginalLiteralLogCellIndex434 hB
      (sourceOriginalGramPrimeProduct434 SB b) ∉ activeB
  let etaA : ℝ := (cA.card:ℝ)*xi
  let etaB : ℝ := (cB.card:ℝ)*xi
  have hwA (a : XA) : 0 ≤ wA a :=
    source_original_physical_gram_prime_mass_nonneg434
      SA muA hmuNonnegA a
  have hwB (b : XB) : 0 ≤ wB b :=
    source_original_physical_gram_prime_mass_nonneg434
      SB muB hmuNonnegB b
  have hmassA : (∑ a : XA, wA a) ≤ 1 :=
    le_of_eq (source_original_physical_gram_prime_mass_total434
      SA muA hmuA)
  have hmassB : (∑ b : XB, wB b) ≤ 1 :=
    le_of_eq (source_original_physical_gram_prime_mass_total434
      SB muB hmuB)
  have hetaA : 0 ≤ etaA := by dsimp [etaA]; positivity
  have hetaB : 0 ≤ etaB := by dsimp [etaB]; positivity
  have hbadA :
      (∑ a : XA, wA a*
        (@ite ℝ (badA a) (Classical.propDecidable (badA a)) 1 0)) ≤
        etaA := by
    have hh : (∑ a : XA,
        if sourceOriginalLiteralLogCellIndex434 hA
              (sourceOriginalGramPrimeProduct434 SA a) ∈ activeA
        then 0 else wA a) ≤ etaA := by
      have hRaw := source_original_physical_discarded_global_mass434
        SA muA hA xi hhA hxi
      exact hRaw
    calc
      _ = (∑ a : XA,
          if sourceOriginalLiteralLogCellIndex434 hA
              (sourceOriginalGramPrimeProduct434 SA a) ∈ activeA
          then 0 else wA a) := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hkeep : sourceOriginalLiteralLogCellIndex434 hA
            (sourceOriginalGramPrimeProduct434 SA a) ∈ activeA
        · simp [badA,hkeep]
        · simp [badA,hkeep]
      _ ≤ etaA := hh
  have hbadB :
      (∑ b : XB, wB b*
        (@ite ℝ (badB b) (Classical.propDecidable (badB b)) 1 0)) ≤
        etaB := by
    have hh : (∑ b : XB,
        if sourceOriginalLiteralLogCellIndex434 hB
              (sourceOriginalGramPrimeProduct434 SB b) ∈ activeB
        then 0 else wB b) ≤ etaB := by
      have hRaw := source_original_physical_discarded_global_mass434
        SB muB hB xi hhB hxi
      exact hRaw
    calc
      _ = (∑ b : XB,
          if sourceOriginalLiteralLogCellIndex434 hB
              (sourceOriginalGramPrimeProduct434 SB b) ∈ activeB
          then 0 else wB b) := by
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hkeep : sourceOriginalLiteralLogCellIndex434 hB
            (sourceOriginalGramPrimeProduct434 SB b) ∈ activeB
        · simp [badB,hkeep]
        · simp [badB,hkeep]
      _ ≤ etaB := hh
  have hL2 :=
    source_original_finite_union_rare_endpoint_L2_sq434
      wA wB hwA hwB hmassA hmassB badA badB
      etaA etaB hetaA hetaB hbadA hbadB f g H hH
  convert hL2 using 1 <;> try ring
  apply congrArg (fun z : ℂ => ‖z‖^2)
  congr 1
  funext q
  have hGate :
      ((sourceOriginalLiteralLogCellIndex434 hA
          (sourceOriginalGramPrimeProduct434 SA q.1) ∉ activeA) ∨
       (sourceOriginalLiteralLogCellIndex434 hB
          (sourceOriginalGramPrimeProduct434 SB q.2) ∉ activeB)) ↔
       badA q.1 ∨ badB q.2 := Iff.rfl
  by_cases hg : badA q.1 ∨ badB q.2
  · have hh : ((sourceOriginalLiteralLogCellIndex434 hA
        (sourceOriginalGramPrimeProduct434 SA q.1) ∉ activeA) ∨
       (sourceOriginalLiteralLogCellIndex434 hB
          (sourceOriginalGramPrimeProduct434 SB q.2) ∉ activeB)) :=
      hGate.mpr hg
    dsimp only [activeA, activeB] at hh
    simp only [if_pos hh, if_pos hg]
    rfl
  · have hh : ¬((sourceOriginalLiteralLogCellIndex434 hA
        (sourceOriginalGramPrimeProduct434 SA q.1) ∉ activeA) ∨
       (sourceOriginalLiteralLogCellIndex434 hB
          (sourceOriginalGramPrimeProduct434 SB q.2) ∉ activeB)) :=
      fun ha => hg (hGate.mp ha)
    dsimp only [activeA, activeB] at hh
    simp only [if_neg hh, if_neg hg]
    rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalAtomTotal -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The genuine SOURCE03 normalized labelled-prime law remains
a normalized probability law after pushforward onto the EXACT
attainable integer-product atom support. Labels with equal
numerical prime products are accounted for in their original
harmonic mass, with no synthetic uniform weights. -/
theorem source_original_physical_atom_support_total434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i, ∑ p ∈ S i, mu i p=1) :
    (∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 S,
      sourceOriginalPhysicalProductAtom434 S mu n) = 1 := by
  have hPush := source_original_physical_atom_real_pushforward434
    S mu (fun _ => (1:ℝ))
  simp only [mul_one] at hPush
  calc
    _ = ∑ a : SourceOriginalGramPrimeTuple434 S,
          sourceOriginalGramPrimeMass434 S mu a := hPush.symm
    _ = 1 := source_original_physical_gram_prime_mass_total434 S mu hmu
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueDiscardedPhysicalA -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The ORIGINAL source03 ν-dependent TARGET free-slot physical
law, with all group-dependent remaining slots present, assigns
at most (#actually attainable A-log-cells)*xi probability to
the event that the chosen product X_A falls outside its TRUE
A-block retained GLOBAL cells. This uses the C153 exact
selected-slot marginal, not an additional independence axiom.
The selected A-probe count can be 1 up to m*|groups|, the
physical t_g vary by ν, and repeated numerical primes remain
legitimate distinct draws. -/
theorem source_original_probe_true_target_A_discarded_mass434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g)
    (h xi : ℝ) (hh : 0 < h) (hxi : 0 < xi) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let mu := sourceOriginalJointHarmonicMu434 BP
      (fun g (p : BP g) => p.val) V
    let active := sourceOriginalProbeActiveCellsA434 m P V ν h xi
    let e := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
    (∑ x : SourceOriginalVariableBIGState434 BP t,
      sourceOriginalVariableBIGMass434 BP t mu x *
        (if sourceOriginalLiteralLogCellIndex434 h
            (∏ z : ν.1, ((x (e z).1 (e z).2).val:ℕ)) ∈ active
         then 0 else (1:ℝ))) ≤
    ((sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) h).card:ℝ)*xi := by
  classical
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let active := sourceOriginalProbeActiveCellsA434 m P V ν h xi
  let e := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
  let S : ν.1 → Finset ℕ := fun z => P z.val.1
  let Vs : ν.1 → ℝ := fun z => V z.val.1
  let F : (∀ z : ν.1, BP z.val.1) → ℝ := fun a =>
    if sourceOriginalLiteralLogCellIndex434 h
      (∏ z : ν.1, (a z).val) ∈ active then 0 else 1
  have hMarg := source_original_probe_true_target_A_marginal434
    J ell m hmJ ν P V hV hVpos F
  have hCellBound := source_original_harmonic_selected_discarded_mass434
    S Vs h xi hh hxi
  have hBound :
      (∑ a : (∀ z : ν.1, BP (e z).1),
        (∏ z : ν.1, mu (e z).1 (a z)) * F a) ≤
      ((sourceOriginalCandidateLogCells434 S h).card:ℝ)*xi := by
    calc
      _ = (∑ a : SourceOriginalGramPrimeTuple434 S,
          (∏ z : ν.1, sourceOriginalHarmonicPrimeMu434
            (fun p : {p : ℕ // p ∈ S z} => p.val)
            (Vs z) (a z)) *
          (if sourceOriginalLiteralLogCellIndex434 h
               (sourceOriginalGramPrimeProduct434 S a) ∈
               sourceOriginalFiniteActiveLogCells434 S
                 (fun z p => sourcePrimeSharedAtom434 (Vs z) p) h xi
           then 0 else (1:ℝ))) := by
        apply Finset.sum_congr
        · ext a
          constructor
          · intro _
            exact Finset.mem_univ a
          · intro _
            exact Finset.mem_univ a
        · intro a ha
          rfl
      _ ≤ ((sourceOriginalCandidateLogCells434 S h).card:ℝ)*xi := by
        exact hCellBound
  change
    (∑ x : SourceOriginalVariableBIGState434 BP t,
      sourceOriginalVariableBIGMass434 BP t mu x *
        F (fun z : ν.1 => x (e z).1 (e z).2)) ≤
      ((sourceOriginalCandidateLogCells434 S h).card:ℝ)*xi
  exact (le_of_eq hMarg).trans hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueDiscardedPhysicalB -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The ORIGINAL source03 ν-dependent SOURCE free-slot physical
law, with all group-dependent remaining slots present, assigns
at most (#actually attainable B-log-cells)*xi probability to
the event that the chosen product X_B falls outside its TRUE
B-block retained GLOBAL cells. This uses the C153 exact
selected-slot marginal, not an additional independence axiom.
The selected B-probe count can be 1 up to m*|groups|, the
physical t_g vary by ν, and repeated numerical primes remain
legitimate distinct draws. -/
theorem source_original_probe_true_source_B_discarded_mass434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g)
    (h xi : ℝ) (hh : 0 < h) (hxi : 0 < xi) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let mu := sourceOriginalJointHarmonicMu434 BP
      (fun g (p : BP g) => p.val) V
    let active := sourceOriginalProbeActiveCellsB434 m P V ν h xi
    let e := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
    (∑ x : SourceOriginalVariableBIGState434 BP t,
      sourceOriginalVariableBIGMass434 BP t mu x *
        (if sourceOriginalLiteralLogCellIndex434 h
            (∏ z : ν.2, ((x (e z).1 (e z).2).val:ℕ)) ∈ active
         then 0 else (1:ℝ))) ≤
    ((sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) h).card:ℝ)*xi := by
  classical
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let active := sourceOriginalProbeActiveCellsB434 m P V ν h xi
  let e := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
  let S : ν.2 → Finset ℕ := fun z => P z.val.1
  let Vs : ν.2 → ℝ := fun z => V z.val.1
  let F : (∀ z : ν.2, BP z.val.1) → ℝ := fun a =>
    if sourceOriginalLiteralLogCellIndex434 h
      (∏ z : ν.2, (a z).val) ∈ active then 0 else 1
  have hMarg := source_original_probe_true_source_B_marginal434
    J ell m hmJ ν P V hV hVpos F
  have hCellBound := source_original_harmonic_selected_discarded_mass434
    S Vs h xi hh hxi
  have hBound :
      (∑ a : (∀ z : ν.2, BP (e z).1),
        (∏ z : ν.2, mu (e z).1 (a z)) * F a) ≤
      ((sourceOriginalCandidateLogCells434 S h).card:ℝ)*xi := by
    calc
      _ = (∑ a : SourceOriginalGramPrimeTuple434 S,
          (∏ z : ν.2, sourceOriginalHarmonicPrimeMu434
            (fun p : {p : ℕ // p ∈ S z} => p.val)
            (Vs z) (a z)) *
          (if sourceOriginalLiteralLogCellIndex434 h
               (sourceOriginalGramPrimeProduct434 S a) ∈
               sourceOriginalFiniteActiveLogCells434 S
                 (fun z p => sourcePrimeSharedAtom434 (Vs z) p) h xi
           then 0 else (1:ℝ))) := by
        apply Finset.sum_congr
        · ext a
          constructor
          · intro _
            exact Finset.mem_univ a
          · intro _
            exact Finset.mem_univ a
        · intro a ha
          rfl
      _ ≤ ((sourceOriginalCandidateLogCells434 S h).card:ℝ)*xi := by
        exact hCellBound
  change
    (∑ x : SourceOriginalVariableBIGState434 BP t,
      sourceOriginalVariableBIGMass434 BP t mu x *
        F (fun z : ν.2 => x (e z).1 (e z).2)) ≤
      ((sourceOriginalCandidateLogCells434 S h).card:ℝ)*xi
  exact (le_of_eq hMarg).trans hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueCellGramMassBridge -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12500000

/-- TRUE literal source03 cell probability under the original
finite product law is exactly the diagonal real Gram cell mass
in the physical labelled-subtype probability space.
This reindexes the SAME prime tuples through an explicit
Fintype equivalence; repeated numerical primes are preserved. -/
theorem source_original_true_cell_probability_eq_gram_mass434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ) :
    sourceOriginalActualCellProbability434 S mu h j =
      sourceOriginalRealGramCellMass434 S mu h j := by
  classical
  let e := sourceFiniteListFamilyEquiv434 S
  let v : (ι → ℕ) → ℝ := fun a =>
    if sourceOriginalLiteralLogCell434 h j (∏ i : ι, a i)
    then sourceSharedLaw434 mu a else 0
  let w : SourceOriginalGramPrimeTuple434 S → ℝ := fun a =>
    if sourceOriginalLiteralLogCell434 h j
        (sourceOriginalGramPrimeProduct434 S a)
    then sourceOriginalGramPrimeMass434 S mu a else 0
  have heq (b : ↑(Fintype.piFinset S)) : v b.val = w (e b) := by
    rfl
  have hsum := Fintype.sum_equiv e
    (fun b : ↑(Fintype.piFinset S) => v b.val)
    w heq
  calc
    _ = ∑ b : ↑(Fintype.piFinset S), v b.val := by
      exact (Finset.sum_coe_sort (Fintype.piFinset S) v).symm
    _ = ∑ a : SourceOriginalGramPrimeTuple434 S, w a := hsum
    _ = _ := by rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalLogCellNaturalCutoff -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12500000

/-- The ACTUAL source03 half-open GLOBAL logarithmic product
cell yields precise NATURAL arithmetic prime cutoffs after
freezing the other-prime product R>0. Lower is floor-1 to
handle endpoint equality; upper is ceil. These are explicit
functions of j,h and the genuine R, not invented fixed windows. -/
noncomputable def sourceOriginalLogCellPrimeLower434
    (h : ℝ) (j : ℤ) (R : ℕ) : ℕ :=
  Nat.floor (Real.exp ((j:ℝ)*h) / (R:ℝ)) - 1

noncomputable def sourceOriginalLogCellPrimeUpper434
    (h : ℝ) (j : ℤ) (R : ℕ) : ℕ :=
  Nat.ceil (Real.exp (((j:ℝ)+1)*h) / (R:ℝ))

/-- Every positive TRUE source BIG prime in the original
global cell on D=pR lies in the exactly specified interval
(a,n] with the movable natural floor/ceil cutoffs above.
The no-rounding-up error is controlled by the one-unit
endpoints, not by enlarging the prime support artificially. -/
theorem source_original_log_cell_prime_natural_interval434
    (h : ℝ) (j : ℤ) (R p : ℕ)
    (hR : 0 < R) (hp : 0 < p)
    (hc : sourceOriginalLiteralLogCell434 h j (p*R)) :
    p ∈ Finset.Ioc
      (sourceOriginalLogCellPrimeLower434 h j R)
      (sourceOriginalLogCellPrimeUpper434 h j R) := by
  have hRpos : (0:ℝ) < R := by exact_mod_cast hR
  have hpRpos : (0:ℝ) < (p*R:ℕ) := by
    exact_mod_cast Nat.mul_pos hp hR
  have hlow : Real.exp ((j:ℝ)*h) ≤ (p:ℝ)*(R:ℝ) := by
    have hh := (Real.exp_le_exp).mpr hc.1
    rw [Real.exp_log hpRpos] at hh
    simpa only [Nat.cast_mul] using hh
  have hupp : (p:ℝ)*(R:ℝ) <
     Real.exp (((j:ℝ)+1)*h) := by
    have hh := (Real.exp_lt_exp).mpr hc.2
    rw [Real.exp_log hpRpos] at hh
    simpa only [Nat.cast_mul] using hh
  have hlowdiv :
      Real.exp ((j:ℝ)*h)/(R:ℝ) ≤ (p:ℝ) :=
    (div_le_iff₀ hRpos).mpr hlow
  have huppdiv :
      (p:ℝ) < Real.exp (((j:ℝ)+1)*h)/(R:ℝ) :=
    (lt_div_iff₀ hRpos).mpr hupp
  have hfloorNonneg :
      0 ≤ Real.exp ((j:ℝ)*h)/(R:ℝ) :=
    (div_nonneg (Real.exp_pos _).le hRpos.le)
  have hfloor :
      Nat.floor (Real.exp ((j:ℝ)*h)/(R:ℝ)) ≤ p := by
    exact_mod_cast ((Nat.floor_le hfloorNonneg).trans hlowdiv)
  have hupper : p ≤
      Nat.ceil (Real.exp (((j:ℝ)+1)*h)/(R:ℝ)) := by
    exact_mod_cast
      (le_of_lt (huppdiv.trans_le (Nat.le_ceil _)))
  unfold sourceOriginalLogCellPrimeLower434
    sourceOriginalLogCellPrimeUpper434
  exact Finset.mem_Ioc.mpr ⟨by omega,hupper⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalLogCellCutoffOrder -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10500000

/-- The original source03 globally chosen positive-width log
cell gives a correctly ordered pair of natural cutoffs
(a,n] for every genuine positive other-prime product R.
The cutoff interval may contain NO primes; the order still
holds without artificially assuming nonempty source cells. -/
theorem source_original_log_cell_prime_cutoffs_order434
    (h : ℝ) (j : ℤ) (R : ℕ)
    (hh : 0 < h) (hR : 0 < R) :
    sourceOriginalLogCellPrimeLower434 h j R ≤
    sourceOriginalLogCellPrimeUpper434 h j R := by
  let lo := Real.exp ((j:ℝ)*h) / (R:ℝ)
  let hi := Real.exp (((j:ℝ)+1)*h) / (R:ℝ)
  have hRpos : (0:ℝ) < R := by exact_mod_cast hR
  have hpositive : 0 ≤ lo :=
    (div_nonneg (Real.exp_pos _).le hRpos.le)
  have hl : lo ≤ hi := by
    dsimp only [lo,hi]
    have hx : (j:ℝ)*h ≤ ((j:ℝ)+1)*h := by
      nlinarith
    have he := Real.exp_le_exp.mpr hx
    exact (div_le_div_iff_of_pos_right hRpos).mpr he
  have hfloor : (Nat.floor lo:ℝ) ≤ lo :=
    Nat.floor_le hpositive
  have hceil : hi ≤ (Nat.ceil hi:ℝ) := Nat.le_ceil hi
  have hcast : Nat.floor lo ≤ Nat.ceil hi := by
    exact_mod_cast (hfloor.trans (hl.trans hceil))
  dsimp only [sourceOriginalLogCellPrimeLower434,
    sourceOriginalLogCellPrimeUpper434]
  exact (Nat.sub_le _ _).trans hcast
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveGramAbelNatural -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The remaining true source03 physical BIG prime product R
is strictly positive whenever each actual BIG marked prime
really lies in its prime support. -/
theorem source_original_gram_other_prime_product_pos434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (i : ι)
    (hprime : ∀ k p, p ∈ S k → p.Prime)
    (r : (k : {k : ι // k ≠ i}) →
      {p : ℕ // p ∈ S k.val}) :
    0 < sourceOriginalGramOtherPrimeProduct434 S i r := by
  unfold sourceOriginalGramOtherPrimeProduct434
  apply Finset.prod_pos
  intro k _
  exact (hprime k.val (r k).val (r k).property).pos

/-- SOURCE03 actual moving-log-cell prime character Gram
step with EXPLICIT floor/ceil natural cutoffs depending
on the ORIGINAL other-prime product R. The previous
'hcover' interval assumption is now discharged from the
true original half-open log cell geometry, with positive h.
The only arithmetic missing premise is an explicit
nonprincipal CHARACTER PREFIX estimate over the genuine
BIG source prime support, not an ideal-operator norm claim.
There is no extra summation loss over BIG tuples. -/
theorem source_original_primitive_gram_actual_cutoff_abel434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (hh : 0 < h) (j : ℤ) (Q : ℕ)
    (c d : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (i : ι)
    (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
    (r : (k : {k : ι // k ≠ i}) →
      {p : ℕ // p ∈ S k.val})
    (B : ℝ) (hB : 0 ≤ B)
    (hPrefix : ∀ k ∈ Finset.Icc
      (sourceOriginalLogCellPrimeLower434 h j
        (sourceOriginalGramOtherPrimeProduct434 S i r))
      (sourceOriginalLogCellPrimeUpper434 h j
        (sourceOriginalGramOtherPrimeProduct434 S i r)),
      ‖sourceOriginalPrimePrefix434
        (sourceOriginalLogCellPrimeLower434 h j
          (sourceOriginalGramOtherPrimeProduct434 S i r)) k
        (sourceOriginalWeightedCellPrimeNumerator434 (S i)
          (mu i)
          (fun p => sourceOriginalLiteralLogCell434 h j
            (p * sourceOriginalGramOtherPrimeProduct434 S i r))
          (fun p => sourceOriginalPrimitivePairQuotient434 Q c d
            (p:ZMod (sourceOriginalPrimitiveCommonLevel434 Q c d))))‖
        ≤ B) :
    ‖sourceOriginalGramLocalPrimeSlice434 S mu h j
      (fun p => c.2 (p:ZMod (c.1.val+1)))
      (fun p => d.2 (p:ZMod (d.1.val+1))) i r‖ ≤
    B / (((sourceOriginalLogCellPrimeLower434 h j
       (sourceOriginalGramOtherPrimeProduct434 S i r)+1:ℕ):ℝ)) := by
  let R := sourceOriginalGramOtherPrimeProduct434 S i r
  have hR : 0 < R :=
    source_original_gram_other_prime_product_pos434
      S i (fun k p hp => (hBIG k p hp).1) r
  let a := sourceOriginalLogCellPrimeLower434 h j R
  let n := sourceOriginalLogCellPrimeUpper434 h j R
  have han : a ≤ n :=
    source_original_log_cell_prime_cutoffs_order434 h j R hh hR
  have hCover : ∀ p ∈ S i,
      sourceOriginalLiteralLogCell434 h j (p*R) →
      p ∈ Finset.Ioc a n := by
    intro p hp hc
    exact source_original_log_cell_prime_natural_interval434
      h j R p hR (hBIG i p hp).1.pos hc
  exact source_original_primitive_gram_local_from_prefix434
    S mu h j Q c d i (hBIG i) r a n han
      hCover B hB hPrefix
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalExactNaturalCellCutoffs -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Exact lower original source03 integer endpoint: no
extra prime added for a floor/ceil rounding safety margin. -/
noncomputable def sourceOriginalLogCellExactLower434
    (h : ℝ) (j : ℤ) (R : ℕ) : ℕ :=
  Nat.ceil (Real.exp ((j:ℝ)*h) / (R:ℝ)) - 1

/-- Exact upper original source03 integer endpoint. The
original GLOBAL cell is half-open on its right side. -/
noncomputable def sourceOriginalLogCellExactUpper434
    (h : ℝ) (j : ℤ) (R : ℕ) : ℕ :=
  Nat.ceil (Real.exp (((j:ℝ)+1)*h) / (R:ℝ)) - 1

/-- An exact number theoretic floor/ceil equivalence:
for natural p>0, a ≤ p < b in REAL coordinates is
precisely the natural half-open interval
(ceil(a)-1, ceil(b)-1]. This is not an interval COVER:
no additional primes enter. -/
theorem source_original_exact_ceil_interval434
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (p : ℕ) (hp : 0 < p) :
    (a ≤ (p:ℝ) ∧ (p:ℝ) < b) ↔
      p ∈ Finset.Ioc (Nat.ceil a-1) (Nat.ceil b-1) := by
  have hca : 0 < Nat.ceil a := Nat.ceil_pos.mpr ha
  have hcb : 0 < Nat.ceil b := Nat.ceil_pos.mpr hb
  constructor
  · rintro ⟨hla,hup⟩
    apply Finset.mem_Ioc.mpr
    constructor
    · have hc : Nat.ceil a ≤ p := Nat.ceil_le.mpr hla
      omega
    · have hc : p < Nat.ceil b := Nat.lt_ceil.mpr hup
      omega
  · intro hh
    have hh' := Finset.mem_Ioc.mp hh
    have hc1 : Nat.ceil a ≤ p := by omega
    have hc2 : p < Nat.ceil b := by omega
    exact ⟨Nat.ceil_le.mp hc1,Nat.lt_ceil.mp hc2⟩

/-- EXACT equivalence for ACTUAL source03 global log-product
cell: on each selected original BIG prime p>0, after all
other genuine source BIG primes are frozen into R>0,
the original GLOBAL half-open logarithmic cell is exactly
the integer interval
  (ceil(exp(j h)/R)-1, ceil(exp((j+1)h)/R)-1].
No enlargement/extra prime at either endpoint and no
hypothesis that h is already small or the cell nonempty. -/
theorem source_original_literal_log_exact_natural_cell434
    (h : ℝ) (j : ℤ) (R p : ℕ)
    (hR : 0 < R) (hp : 0 < p) :
    sourceOriginalLiteralLogCell434 h j (p*R) ↔
      p ∈ Finset.Ioc
        (sourceOriginalLogCellExactLower434 h j R)
        (sourceOriginalLogCellExactUpper434 h j R) := by
  have hRpos : (0:ℝ) < (R:ℝ) := by exact_mod_cast hR
  have hpRpos : (0:ℝ) < ((p*R:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos hp hR
  have hexp : Real.exp (Real.log ((p*R:ℕ):ℝ)) =
      ((p*R:ℕ):ℝ) := Real.exp_log hpRpos
  have hlog :
      sourceOriginalLiteralLogCell434 h j (p*R) ↔
        (Real.exp ((j:ℝ)*h) ≤ ((p*R:ℕ):ℝ) ∧
         ((p*R:ℕ):ℝ) < Real.exp (((j:ℝ)+1)*h)) := by
    unfold sourceOriginalLiteralLogCell434
    constructor
    · rintro ⟨hl,hu⟩
      exact ⟨by rw [← hexp]; exact Real.exp_le_exp.mpr hl,
        by rw [← hexp]; exact Real.exp_lt_exp.mpr hu⟩
    · rintro ⟨hl,hu⟩
      exact ⟨Real.exp_le_exp.mp (by simpa only [hexp] using hl),
        Real.exp_lt_exp.mp (by simpa only [hexp] using hu)⟩

  have hdiv :
      (Real.exp ((j:ℝ)*h) ≤ ((p*R:ℕ):ℝ) ∧
       ((p*R:ℕ):ℝ) < Real.exp (((j:ℝ)+1)*h)) ↔
      (Real.exp ((j:ℝ)*h)/(R:ℝ) ≤ (p:ℝ) ∧
       (p:ℝ) < Real.exp (((j:ℝ)+1)*h)/(R:ℝ)) := by
    constructor
    · rintro ⟨hl,hu⟩
      exact ⟨(div_le_iff₀ hRpos).mpr
        (by simpa only [Nat.cast_mul] using hl),
        (lt_div_iff₀ hRpos).mpr
        (by simpa only [Nat.cast_mul] using hu)⟩
    · rintro ⟨hl,hu⟩
      exact ⟨by
        have hs := (div_le_iff₀ hRpos).mp hl
        simpa only [Nat.cast_mul] using hs,
        by
        have hs := (lt_div_iff₀ hRpos).mp hu
        simpa only [Nat.cast_mul] using hs⟩
  rw [hlog,hdiv]
  have hlo : 0 < Real.exp ((j:ℝ)*h)/(R:ℝ) :=
    div_pos (Real.exp_pos _) hRpos
  have hhi : 0 < Real.exp (((j:ℝ)+1)*h)/(R:ℝ) :=
    div_pos (Real.exp_pos _) hRpos
  exact source_original_exact_ceil_interval434
    _ _ hlo hhi p hp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalExactPrimeBandCell -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The ACTUAL source BIG group prime band is an interval
of primes (u,v], not a synthetic finite prime support with
unrelated arbitrary holes. -/
def sourceOriginalActualPrimeBand434 (u v : ℕ) : Finset ℕ :=
  (Finset.Ioc u v).filter Nat.Prime

/-- The original GLOBAL product log-cell, restricted to the
real BIG prime band, is EXACTLY one moving arithmetic
prime interval determined by the other-prime product R.
No extra prime at lower/upper integer boundary and no
independent per-prime cell substitution. -/
theorem source_original_actual_band_global_cell_eq434
    (u v R : ℕ) (hR : 0 < R) (h : ℝ) (j : ℤ) :
    (sourceOriginalActualPrimeBand434 u v).filter
      (fun p => sourceOriginalLiteralLogCell434 h
        j (p*R)) =
    (Finset.Ioc
      (max u (sourceOriginalLogCellExactLower434 h
        j R))
      (min v (sourceOriginalLogCellExactUpper434 h
        j R))).filter Nat.Prime := by
  classical
  ext p
  simp only [sourceOriginalActualPrimeBand434, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hband,hprime⟩,hcell⟩
    have hb := Finset.mem_Ioc.mp hband
    have he := Finset.mem_Ioc.mp
      ((source_original_literal_log_exact_natural_cell434
        h j R p hR hprime.pos).mp hcell)
    refine ⟨Finset.mem_Ioc.mpr ?_,hprime⟩
    exact ⟨max_lt_iff.mpr ⟨hb.1,he.1⟩,
      le_min_iff.mpr ⟨hb.2,he.2⟩⟩
  · rintro ⟨hinterval,hprime⟩
    obtain ⟨hu,hl⟩ :=
      max_lt_iff.mp (Finset.mem_Ioc.mp hinterval).1
    obtain ⟨hv,hr⟩ :=
      le_min_iff.mp (Finset.mem_Ioc.mp hinterval).2
    refine ⟨⟨Finset.mem_Ioc.mpr ⟨hu,hv⟩,hprime⟩,?_⟩
    exact (source_original_literal_log_exact_natural_cell434
      h j R p hR hprime.pos).mpr
        (Finset.mem_Ioc.mpr ⟨hl,hr⟩)
end Green64Analytic.CorrelationSquare

end

