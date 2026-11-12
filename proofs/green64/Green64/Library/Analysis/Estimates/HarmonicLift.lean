module

public import Green64.Library.Weights.HiddenSelectedEnergy
public import Green64.Library.Weights.Part054

@[expose] public section

/-!
# Analysis / Estimates / HarmonicLift

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualHarmonicLift -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6000000
variable {G : Type} [Fintype G] [DecidableEq G]

/-- The actual harmonic selected-coordinate lift, normalized by sqrt D.
Its hidden factor contains EVERY hidden base/opposite-block slot. -/
def b580ActualHiddenSelectedLift
    (P : G → Finset ℕ) (c r : G → ℕ) (V : G → ℝ)
    (q D : ℝ) (n : ℕ) (f : (∀ g,Fin (c g) → ℕ) → ℂ)
    (a : ∀ g,Fin (c g) → ℕ) : ℂ :=
  (((b580HiddenAllFactor q c r (fun g => smallPrimeCount (P g) n) V *
      b579SelectedPrimeProduct c a) / Real.sqrt D : ℝ):ℂ) * f a

/-- Full literal original marked decoration equals the harmonic average
of the actual normalized selected lift, with the NECESSARY sqrt D
restored outside. This prevents a silent loss of auxiliary normalization. -/
theorem b580_actual_marked_eq_harmonic_hidden_lift
    (P : G → Finset ℕ) (t c r : G → ℕ) (V : G → ℝ)
    (q D : ℝ) (n : ℕ)
    (s : ∀ g,Fin (c g) → Fin (t g))
    (hs : ∀ g,Function.Injective (s g))
    (ht : ∀ g,t g=c g+r g)
    (hP : ∀ g p,p∈P g → 0<p) (hV : ∀ g,0<V g) (hD : 0<D)
    (f : (∀ g,Fin (c g) → ℕ) → ℂ) :
    actualBigMarkDecoration P t q V
      (fun a => f (fun g i => a g (s g i))) n =
      (Real.sqrt D:ℂ) * ∑ a∈bigMarkLists P c n,
        (b579SelectedHarmonicMass c V a:ℂ) *
          b580ActualHiddenSelectedLift P c r V q D n f a := by
  rw [b580_original_marked_observed_slot_marginal P t c r V q n s hs ht f]
  let B := b580HiddenAllFactor q c r (fun g => smallPrimeCount (P g) n) V
  let A := ∏ g,(V g)^(c g)
  have hS : Real.sqrt D≠0 := (Real.sqrt_pos.mpr hD).ne'
  change (B:ℂ)*(∑ a∈bigMarkLists P c n,f a)/(A:ℂ) = _
  calc
    _ = ∑ a∈bigMarkLists P c n,((B/A:ℝ):ℂ)*f a := by
      rw [Complex.ofReal_div,←Finset.mul_sum]
      ring
    _ = ∑ a∈bigMarkLists P c n,
        (Real.sqrt D:ℂ)*((b579SelectedHarmonicMass c V a:ℂ)*
          b580ActualHiddenSelectedLift P c r V q D n f a) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hpositive : ∀ g i,0<a g i := by
        intro g i
        have hg := Fintype.mem_piFinset.mp ha g
        have hi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hg).1 i
        exact hP g _ (Finset.mem_filter.mp hi).1
      have hden := b579_selected_harmonic_density c V a hV hpositive
      have hcoef : B/A=Real.sqrt D*b579SelectedHarmonicMass c V a*
          (B*b579SelectedPrimeProduct c a/Real.sqrt D) := by
        calc
          _ = B*(b579SelectedHarmonicMass c V a*b579SelectedPrimeProduct c a) := by
            rw [hden]
            dsimp [A]
            ring
          _ = _ := by field_simp
      change ((B/A:ℝ):ℂ)*f a =
        (Real.sqrt D:ℂ)*((b579SelectedHarmonicMass c V a:ℂ)*
          (((B*b579SelectedPrimeProduct c a/Real.sqrt D:ℝ):ℂ)*f a))
      rw [hcoef]
      push_cast
      ring
    _ = _ := by rw [Finset.mul_sum]

/-- The squared Hilbert norm of the ACTUAL normalized lift is exactly
the energy bounded by B580. No auxiliary product or harmonic density
is silently removed from the norm. -/
theorem b580_actual_hidden_lift_norm_sum
    (P : G → Finset ℕ) (c r : G → ℕ) (V : G → ℝ)
    (q D : ℝ) (n : ℕ) (f : (∀ g,Fin (c g) → ℕ) → ℂ) (hD : 0<D) :
    (∑ a∈bigMarkLists P c n,
      b579SelectedHarmonicMass c V a*
        ‖b580ActualHiddenSelectedLift P c r V q D n f a‖^2) =
      b580ActualHiddenSelectedEnergy P c r V q D n f := by
  unfold b580ActualHiddenSelectedEnergy
  apply Finset.sum_congr rfl
  intro a ha
  simp only [b580ActualHiddenSelectedLift,norm_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow,Real.sq_sqrt hD.le]
  ring


private theorem b580_original_mark_ne_aux_of_coprime
    (P : G → Finset ℕ) (t : G → ℕ) (D n p : ℕ)
    (hp : p.Prime) (hpD : p∣D) (hDn : Nat.Coprime D n)
    (a : ∀ g,Fin (t g) → ℕ) (ha : a∈bigMarkLists P t n) :
    ∀ g i,a g i≠p := by
  intro g i he
  have hg := Fintype.mem_piFinset.mp ha g
  have hi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hg).1 i
  have hd := (Finset.mem_filter.mp hi).2
  rw [he] at hd
  have hgp : p∣Nat.gcd D n := Nat.dvd_gcd hpD hd
  have hcop : Nat.gcd D n=1 := hDn
  rw [hcop] at hgp
  exact hp.ne_one (Nat.dvd_one.mp hgp)

/-- The ACTUAL B574 full free/auxiliary ban follows on clean physical
endpoints, for every original divisor list including all hidden marks.
Auxiliary values may repeat. No ban is dropped outside this scope. -/
theorem b580_actual_free_aux_ban_of_coprime
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (D w wp : ℕ) (hPrime : ∀ z,(aux z).Prime) (hAuxD : ∀ z,aux z∣D)
    (hw : Nat.Coprime D w) (hwp : Nat.Coprime D wp)
    (a b : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (ha : a∈bigMarkLists P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) w)
    (hb : b∈bigMarkLists P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) wp) :
    sourceB574FreeAuxBan434 J ell m hmJ nu aux a b := by
  intro z i
  constructor
  · exact (b580_original_mark_ne_aux_of_coprime P _ D w (aux z)
      (hPrime z) (hAuxD z) hw a ha (sourceOriginalProbeAuxGroup434 m nu z) i).symm
  · exact (b580_original_mark_ne_aux_of_coprime P _ D wp (aux z)
      (hPrime z) (hAuxD z) hwp b hb (sourceOriginalProbeAuxGroup434 m nu z) i).symm

/-- Clean-sector equality retains the SAME physical canonical Kν.
The hidden-slot marginal may be applied to that original Kν only after
this full-list ban theorem (or an equivalent checked clean premise). -/
theorem b580_actual_clean_free_kernel_eq_original
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (D w wp : ℕ) (hPrime : ∀ z,(aux z).Prime) (hAuxD : ∀ z,aux z∣D)
    (hw : Nat.Coprime D w) (hwp : Nat.Coprime D wp)
    (a b : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (ha : a∈bigMarkLists P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) w)
    (hb : b∈bigMarkLists P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) wp) :
    sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux a b =
      sourceOriginalProbeCanonicalKnu434 J ell m hmJ nu Q hA hB xi P V aux a b := by
  unfold sourceB574CanonicalFreeKernel434
  rw [if_pos (b580_actual_free_aux_ban_of_coprime
    J ell m hmJ nu P aux D w wp hPrime hAuxD hw hwp a b ha hb)]
end Green64Analytic.CorrelationSquare

end

end

