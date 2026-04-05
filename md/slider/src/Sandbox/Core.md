
<div class="lean-code" data-start-line="1" data-end-line="3"><pre><code>theorem x {p: Prop}: p ∨ ¬p := by grind

#print axioms x -- &#x27;x&#x27; depends on axioms: [propext, Classical.choice, Quot.sound]</code></pre></div>


License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

