
theory test = Main:

lemma foo:
"((x_post::int) = x_pre &
 (y_post::int) = x_pre + y_pre &
 (z_post::int) = z_pre + y_post) =
(EX x_1 y_1 z_1.
(x_1 = x_pre &
 y_1 = y_pre + x_pre &
 z_1 = z_pre)
&
(x_post = x_1 &
y_post = y_1 &
z_post = z_1 + y_1)
)"
apply auto

end