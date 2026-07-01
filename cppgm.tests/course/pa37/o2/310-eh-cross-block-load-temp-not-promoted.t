declare function @may_throw() -> void [binding=strong]
declare function @sink(%arg0 : ptr) -> void [binding=strong]

function @f(%this : ptr) -> void [binding=strong] {
  slot $this : ptr

  block ^entry:
    store ptr %this, $this
    %t1 = load ptr $this
    eh_try ^cleanup
    call void @may_throw()
    eh_end
    jump ^after

  block ^cleanup:
    call void @sink(%t1)
    resume

  block ^after:
    call void @sink(%t1)
    return void
}
