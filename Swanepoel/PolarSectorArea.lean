module
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory Set

def polarSector (r a b : ℝ) : Set (ℝ×ℝ) :=
  polarCoord.symm '' (Ioo 0 r ×ˢ Ioo a b)

theorem polarSector_area {r a b : ℝ} (hr : 0<r) (hab : a<b)
    (ha : -Real.pi≤a) (hb : b≤Real.pi) :
    volume.real (polarSector r a b)=r^2*(b-a)/2 := by
  have hs : MeasurableSet (Ioo (0:ℝ) r ×ˢ Ioo a b) := measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : Ioo (0:ℝ) r ×ˢ Ioo a b ⊆ polarCoord.target := by
    rintro ⟨s,t⟩ ⟨hs,ht⟩
    exact ⟨hs.1,lt_of_le_of_lt ha ht.1,lt_of_lt_of_le ht.2 hb⟩
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    (polarCoord.symm.injOn.mono hsub) (fun _ : ℝ×ℝ => (1:ℝ))
  have harea : volume.real (polarSector r a b)=
      ∫ p in Ioo (0:ℝ) r ×ˢ Ioo a b,|p.1| := by
    simpa only [polarSector,setIntegral_const,smul_eq_mul,mul_one,det_fderivPolarCoordSymm] using hchange
  have hid : (∫ s in Ioo (0:ℝ) r,s)=r^2/2 := by
    rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hr.le,integral_id]
    ring
  have hangle : (∫ t in Ioo a b,(1:ℝ))=b-a := by
    simp [measureReal_def,Real.volume_Ioo,ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  rw [harea]
  calc
    _ = ∫ p in Ioo (0:ℝ) r ×ˢ Ioo a b,p.1*(1:ℝ) := by
      apply setIntegral_congr_fun hs
      intro p hp
      change |p.1|=p.1*1
      rw [abs_of_pos hp.1.1,mul_one]
    _ = (∫ s in Ioo (0:ℝ) r,s)*(∫ t in Ioo a b,(1:ℝ)) :=
      setIntegral_prod_mul (fun s : ℝ => s) (fun _ : ℝ => (1:ℝ)) _ _
    _ = r^2*(b-a)/2 := by rw [hid,hangle]; ring

theorem half_radius_polarSector_area {a b : ℝ} (hab : a<b)
    (ha : -Real.pi≤a) (hb : b≤Real.pi) :
    volume.real (polarSector (1/2) a b)=(b-a)/8 := by
  rw [polarSector_area (by norm_num) hab ha hb]
  ring

end Swanepoel
