import SystemE
import Book.Prop34

namespace Elements.Book1

theorem proposition_43 : ∀ (a b c d e f g h k : Point) (AD BC AB CD AC EF GH : Line),
  formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC ∧ k.onLine AC ∧
  between a h d ∧ formParallelogram a h e k AD EF AB GH ∧ formParallelogram k f g c EF BC GH CD →
  ((△ e:b:g : ℝ) + △ e:g:k = △ h:k:f + △ h:f:d) :=
by
  euclid_intros
  euclid_apply (proposition_34 d a c b AD BC CD AB AC)
  euclid_apply (proposition_34 h a k e AD EF GH AB AC)
  euclid_apply (proposition_34 f k c g EF BC CD GH AC)
  euclid_assert (△ a:e:k : ℝ) + (△ k:g:c) = (△ a:h:k) + (△ k:f:c)
  euclid_assert (△ a:h:k : ℝ) + (△ k:f:c) + (△ h:k:f) + (△ h:f:d) = (△ d:a:c)
  euclid_finish

end Elements.Book1
