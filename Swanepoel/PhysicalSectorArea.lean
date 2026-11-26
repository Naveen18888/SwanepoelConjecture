module
public import Swanepoel.PolarSectorArea
public import Swanepoel.ActualCornerAngles
public import Mathlib.Analysis.Complex.Isometry
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory Set

def planeComplexIsometry : Plane ≃ₗᵢ[ℝ] ℂ :=
  { LinearEquiv.ofBijective planeComplex ⟨planeComplex_injective,by
      intro z
      refine ⟨WithLp.toLp 2 ![z.re,z.im],?_⟩
      apply Complex.ext <;> simp [planeComplex]⟩ with
    norm_map' := planeComplex_norm }

theorem planeComplex_isometry_symm (z : ℂ) :
    planeComplex (planeComplexIsometry.symm z)=z :=
  planeComplexIsometry.apply_symm_apply z

def unitAngleCircle (ρ : ℝ) : Circle :=
  ⟨planeComplex (unitAngleVector ρ),mem_sphere_zero_iff_norm.mpr
    ((planeComplex_norm (unitAngleVector ρ)).trans (unitAngleVector_norm ρ))⟩

def sectorChart (p : Plane) (ρ : ℝ) : (ℝ×ℝ) ≃ᵐ Plane :=
  (Complex.measurableEquivRealProd.symm.trans
    (((rotation (unitAngleCircle ρ)).trans planeComplexIsometry.symm).toHomeomorph.toMeasurableEquiv)).trans
      (Homeomorph.addLeft p).toMeasurableEquiv

theorem sectorChart_preserves_volume (p : Plane) (ρ : ℝ) :
    MeasurePreserving (sectorChart p ρ) := by
  exact (measurePreserving_add_left volume p).comp
    ((((rotation (unitAngleCircle ρ)).trans planeComplexIsometry.symm).measurePreserving).comp
      Complex.volume_preserving_equiv_real_prod.symm)

theorem sectorChart_complex (p : Plane) (ρ : ℝ) (z : ℝ×ℝ) :
    planeComplex (sectorChart p ρ z)=planeComplex p+
      planeComplex (unitAngleVector ρ)*Complex.equivRealProd.symm z := by
  change planeComplex (p+planeComplexIsometry.symm
    (rotation (unitAngleCircle ρ) (Complex.measurableEquivRealProd.symm z)))= _
  rw [map_add,planeComplex_isometry_symm]
  rfl

theorem sectorChart_polar (p : Plane) (ρ r θ : ℝ) :
    sectorChart p ρ (polarCoord.symm (r,θ))=
      p+r • unitAngleVector (ρ+3*θ/Real.pi) := by
  apply planeComplex_injective
  rw [sectorChart_complex,map_add,map_smul]
  have hphase : Real.pi/3*(ρ+3*θ/Real.pi)=Real.pi/3*ρ+θ := by
    field_simp
  apply Complex.ext <;>
    simp [planeComplex,unitAngleVector,polarCoord,Complex.real_smul,hphase,
      Real.cos_add,Real.sin_add,-Complex.ofReal_cos,-Complex.ofReal_sin] <;> ring

def cornerSectorPatch (p : Plane) (ρ g : ℝ) : Set Plane :=
  sectorChart p (ρ-g/2) '' polarSector (1/2) (-Real.pi*g/6) (Real.pi*g/6)

theorem cornerSectorPatch_area (p : Plane) (ρ g : ℝ) (hg0 : 0<g) (hg6 : g<6) :
    volume.real (cornerSectorPatch p ρ g)=Real.pi*g/24 := by
  have hp : 0<Real.pi := Real.pi_pos
  have harea := half_radius_polarSector_area
    (a := -Real.pi*g/6) (b := Real.pi*g/6)
    (by nlinarith) (by nlinarith) (by nlinarith)
  have hpreimage : (sectorChart p (ρ-g/2)) ⁻¹'
      (sectorChart p (ρ-g/2) '' polarSector (1/2) (-Real.pi*g/6) (Real.pi*g/6))=
        polarSector (1/2) (-Real.pi*g/6) (Real.pi*g/6) :=
    Set.preimage_image_eq _ (sectorChart p (ρ-g/2)).injective
  have hmeasure := (sectorChart_preserves_volume p (ρ-g/2)).measure_preimage_equiv
    (cornerSectorPatch p ρ g)
  change volume ((sectorChart p (ρ-g/2)) ⁻¹'
    (sectorChart p (ρ-g/2) '' polarSector (1/2) (-Real.pi*g/6) (Real.pi*g/6)))=
      volume (cornerSectorPatch p ρ g) at hmeasure
  rw [hpreimage] at hmeasure
  rw [measureReal_def,← hmeasure,← measureReal_def,harea]
  ring

end Swanepoel
