
<div class="lean-code" data-start-line="1" data-end-line="7"><pre><code>universe u

def idPi : Π (α : Type u), α → α := fun _ x =&gt; x

def idForall : ∀ (α : Type u), α → α := fun _ x =&gt; x

def idAscii : forall (α : Type u), α → α := fun _ x =&gt; x</code></pre></div>


License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

