declare function @sink(%p : ptr) -> void [binding=strong, unwind=no]

function @wrap(%p : ptr) -> ptr [prefer_local=yes] {
  slot $__it : ptr

  block ^entry:
    store ptr %p, $__it
    call void @sink($__it)
    return ptr %p
}

function @main(%a : ptr, %b : ptr) -> ptr {
  block ^entry:
    %x = call ptr @wrap(%a)
    %y = call ptr @wrap(%b)
    return ptr %y
}
