
TODO
===


```lean
namespace ReflexiveGraph

class CartesianClosed.{u} (C : Type u) (terminal : C) extends
      Category C, HasProduct C, HasExp C, HasTerminalObject C terminal

instance inst_ccc : CartesianClosed ReflexiveGraph terminus' := {}

--hide
end ReflexiveGraph
end LeanW26
--unhide
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

