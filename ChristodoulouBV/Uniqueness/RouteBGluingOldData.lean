module

public import ChristodoulouBV.Uniqueness.RouteBGluingOldMatch
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Initial edge of the closed old piece

Finite-cutoff matching gives the prescribed initial values below the
terminal level. Continuity of the closed old fields and of the initial
profile extends them to both endpoints.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A closed old C¹ representative matching the finite family retains the
prescribed initial radius and outgoing scalar derivative through `vStar`. -/
theorem routeB_old_initial_data_of_finite_match
    {alpha₀ : ℝ → ℝ} {a vStar : ℝ} {S : ℝ → Fields} {SOld : Fields}
    (ha : 0 < a) (haStar : a < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ d ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge d) (S d) ∧
      (∀ v ∈ Ioo (0 : ℝ) d,
        (S d).r 0 v = v / 2 ∧ (S d).alpha 0 v = alpha₀ v))
    (hOldC1 : RouteBFieldsC1On SOld (routeBOldRegion a vStar))
    (hMatch : ∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
      RouteBFieldsEqOn SOld (routeBCanonicalOldFields d (S d))
        (routeBOldRegion a e)) :
    ∀ v ∈ Icc (0 : ℝ) vStar,
      SOld.r 0 v = v / 2 ∧ SOld.alpha 0 v = alpha₀ v := by
  let J := Icc (0 : ℝ) vStar
  have hmap : MapsTo (fun v : ℝ => (0, v)) J
      (routeBOldRegion a vStar) := by
    intro v hv
    exact mem_routeBOldRegion.mpr ⟨le_rfl, ha.le, hv.1, hv.2⟩
  have hpair : ContinuousOn (fun v : ℝ => ((0 : ℝ), v)) J :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hRCont : ContinuousOn (fun v => SOld.r 0 v) J :=
    (hOldC1 .radius).continuousOn.comp hpair hmap
  have hACont : ContinuousOn (fun v => SOld.alpha 0 v) J :=
    (hOldC1 .outgoing).continuousOn.comp hpair hmap
  have hαCont : ContinuousOn alpha₀ J :=
    hα.continuousOn.mono (fun _ hv => hv.1)
  have hOpen : ∀ v ∈ Ioo (0 : ℝ) vStar,
      SOld.r 0 v = v / 2 ∧ SOld.alpha 0 v = alpha₀ v := by
    intro v hv
    let t := max a v
    let e := (t + vStar) / 2
    let d := (e + vStar) / 2
    have ht : t < vStar := max_lt haStar hv.2
    have hte : t < e := by dsimp [e]; linarith only [ht]
    have heStar : e < vStar := by dsimp [e]; linarith only [ht]
    have he : e ∈ Ioo a vStar :=
      ⟨(le_max_left a v).trans_lt hte, heStar⟩
    have hve : v ≤ e := (le_max_right a v).trans hte.le
    have hed : d ∈ Ioo e vStar := by
      dsimp [d]
      constructor <;> linarith only [heStar]
    have hd : d ∈ Ioo (0 : ℝ) vStar :=
      ⟨ha.trans (he.1.trans hed.1), hed.2⟩
    have hp : (0, v) ∈ routeBOldRegion a e :=
      mem_routeBOldRegion.mpr ⟨le_rfl, ha.le, hv.1.le, hve⟩
    have hvd : v ∈ Ioo (0 : ℝ) d :=
      ⟨hv.1, hve.trans_lt hed.1⟩
    have hdata := (hfamily d hd).2 v hvd
    have hr := hMatch e he d hed .radius hp
    have hA := hMatch e he d hed .outgoing hp
    have hcanon := C1Solution.canonicalRadius_eq_radius
      (ha.trans he.1) hed.1 (hfamily d hd).1
      le_rfl hv.1 hve
    exact ⟨hr.trans (hcanon.trans hdata.1), hA.trans hdata.2⟩
  have hROpen : EqOn (fun v => SOld.r 0 v) (fun v => v / 2)
      (Ioo (0 : ℝ) vStar) := fun v hv => (hOpen v hv).1
  have hAOpen : EqOn (fun v => SOld.alpha 0 v) alpha₀
      (Ioo (0 : ℝ) vStar) := fun v hv => (hOpen v hv).2
  have hR : EqOn (fun v => SOld.r 0 v) (fun v => v / 2) J :=
    hROpen.of_subset_closure
      hRCont (by fun_prop) Ioo_subset_Icc_self
      (by rw [closure_Ioo (ne_of_lt (ha.trans haStar))])
  have hA : EqOn (fun v => SOld.alpha 0 v) alpha₀ J :=
    hAOpen.of_subset_closure
      hACont hαCont Ioo_subset_Icc_self
      (by rw [closure_Ioo (ne_of_lt (ha.trans haStar))])
  exact fun v hv => ⟨hR hv, hA hv⟩

end ChristodoulouBV.Uniqueness

end
