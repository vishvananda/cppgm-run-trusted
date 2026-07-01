declare function @may_throw() -> void [binding=strong]

global @depth : i32 [binding=strong] = 0

function @f() -> i32 [binding=strong] {
  slot $entered : u8

  block ^entry:
    store u8 0, $entered
    eh_try ^catch_dispatch
    store u8 1, $entered
    call void @may_throw()
    store u8 0, $entered
    eh_end
    return i32 1

  block ^catch_dispatch:
    eh_catch_all
    jump ^catch_body

  block ^catch_body:
    %flag = load u8 $entered
    branch %flag, ^undo, ^done

  block ^undo:
    %old = load i32 @depth
    %new = binary sub i32 %old, 1
    store i32 %new, @depth
    jump ^done

  block ^done:
    return i32 0
}
