module
public import Swanepoel.L38AnisotropicQuadrature
public import Swanepoel.L38SupportAreaCertificate
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem l38_slice_calibration {ι : Type*} [Fintype ι]
    (next : Equiv.Perm ι) (hcycle : next.IsCycleOn Set.univ) (p : ι→Plane)
    (C : Set Plane) (hC : Convex ℝ C) (hclosed : IsClosed C)
    (h : ℝ→ℝ) (hcont : Continuous h) (a b : ℝ)
    (hgraph : ∀ x∈Icc a b,cartPoint x (h x)∈C ∧ cartPoint x (-h x)∈C)
    (hpos : ∀ x∈Icc a b,0≤h x) (hp : ∀ i,p i 0∈Icc a b)
    (imin imax : ι) (hmin : p imin 0=a) (hmax : p imax 0=b)
    (cost : ι→ℝ) (hsupport : ∀ i,∀ q∈C,cross2 q (p (next i)-p i)≤cost i) :
    4*(2*(∫ x in a..b,h x))*cyclicSignedArea next p≤(∑ i,cost i)^2 := by
  have hqexists (i : ι) := l38_exists_slice_quadrature C hC hclosed h hcont a b
    hgraph hpos (hp i) (hp (next i))
  choose q hq hqx hmoment using hqexists
  obtain ⟨S,hS⟩ := l38_exists_cyclic_arc_sum next hcycle imin imax
    (fun i => l38SlicePrimitive h a (p i 0))
  rw [hmax,hmin,l38SlicePrimitive_sub h hcont] at hS
  have hab : a≤b := (hp imin).1.trans (hp imin).2
  have hw : 0≤2*(∫ x in a..b,h x) :=
    mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg hab hpos)
  have hcal := finite_walk_support_calibration next p q cost (fun _ => 0)
    (l38SlicePrimitive h a) S 1 (2*(∫ x in a..b,h x)) hw hqx
    (fun i => by simpa only [sub_self,zero_sub] using hmoment i)
    (by simpa only [one_pow,one_mul,hS] using le_refl (2*(∫ x in a..b,h x)))
    (fun i => by simpa only [one_mul] using hsupport i (q i) (hq i))
  exact hcal

theorem l38_cross_eq_inner_rightNormal (q e : Plane) :
    cross2 q e=inner ℝ q (rightNormalMap e) := by
  simp [cross2,rightNormalMap,quarterTurn,PiLp.inner_apply,Fin.sum_univ_two]; ring

theorem l38_certificate_edge_support (q d : Plane) (hq : q∈l38CertificateBody)
    (hd : ‖d‖=1) (l : ℝ) (hl : 0≤l) (bank : Prop) [Decidable bank]
    (hbank : bank → rightNormalMap d∈l38BankArc l38SupportAxis) :
    cross2 q (l • d) ≤ if bank then l/3 else l := by
  rw [cross2_smul_right,l38_cross_eq_inner_rightNormal]
  by_cases hb : bank
  · rw [ite_eq_left hb]
    have hh := mul_le_mul_of_nonneg_left (hq.2 _ (hbank hb)) hl
    linarith only [hh]
  · rw [ite_eq_right hb]
    have hh := l38SupportBody_return_bound (l38BankArc l38SupportAxis) hq
      ((rightNormalMap_norm d).trans hd)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hl

theorem l38_normalized_bank_area_bound {ι : Type*} [Fintype ι]
    (next : Equiv.Perm ι) (hcycle : next.IsCycleOn Set.univ) (p : ι→Plane)
    (hp : ∀ i,p i 0∈Icc (-1) (1/3))
    (imin imax : ι) (hmin : p imin 0= -1) (hmax : p imax 0=1/3)
    (bank : ι→Prop) (l : ι→ℝ) (d : ι→Plane)
    (hl : ∀ i,0≤l i) (hd : ∀ i,‖d i‖=1)
    (hedge : ∀ i,p (next i)-p i=l i • d i)
    (hbank : ∀ i,bank i → rightNormalMap (d i)∈l38BankArc l38SupportAxis) :
    4*l38CertificateArea*cyclicSignedArea next p≤
      (∑ i,if bank i then l i/3 else l i)^2 := by
  have hcal := l38_slice_calibration next hcycle p l38CertificateBody
    (l38SupportBody_convex _ _) (l38SupportBody_isClosed _ _)
    l38CertificateHeight l38_certificate_height_continuous (-1) (1/3)
    (fun _ hx => l38_certificate_graphs_support hx)
    (fun _ hx => l38_certificate_height_nonneg hx) hp imin imax hmin hmax
    (fun i => if bank i then l i/3 else l i) (by
      intro i q hq
      rw [hedge i]
      exact l38_certificate_edge_support q (d i) hq (hd i) (l i) (hl i) (bank i) (hbank i))
  rw [l38_certificate_height_integral] at hcal
  exact hcal

end Swanepoel
