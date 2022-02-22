(set-logic ALL)

(declare-datatypes ((Option 1))
  ((par (T) ((Some (value T))
             (None)))))

(declare-datatypes ((Mode 0)) ((
  (SeL4)
  (SeL4_Only)
  (SeL4_TB))))

(declare-datatypes ((ComponentCategory 0)) ((
  (Abstract)
  (Bus)
  (Data)
  (Device)
  (Memory)
  (Process)
  (Processor)
  (Subprogram)
  (SubprogramGroup)
  (System)
  (Thread)
  (ThreadGroup)
  (VirtualBus)
  (VirtualProcessor))))

(declare-datatypes ((DispatchProtocol 0)) ((
  (Periodic)
  (Sporadic))))

(declare-datatypes ((SchedulingType 0)) ((
  (Pacing)
  (SelfPacing)
  (PeriodicDispatching)
  (UNSPECIFIED_SCHEDULING_TYPE))))

(declare-datatypes ((Direction 0)) ((
  (In)
  (Out)
  (InOut))))

(declare-datatypes ((FeatureCategory 0)) ((
  (AbstractFeature)
  (BusAccess)
  (DataAccess)
  (DataPort)
  (EventPort)
  (EventDataPort)
  (FeatureGroup)
  (Parameter)
  (SubprogramAccess)
  (SubprogramAccessGroup))))


(declare-const CodegenMode Mode)
(assert (= CodegenMode SeL4_Only))

(declare-const ModelSchedulingType SchedulingType)
(assert (= ModelSchedulingType Pacing))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                        ;;
;;                                AADL Model                              ;;
;;                                                                        ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-datatypes ((AadlComponent 0)) ((
  (top_impl_Instance_src_process)
  (top_impl_Instance_vm_src_proc)
  (top_impl_Instance_dst_process)
  (top_impl_Instance_vm_dst_proc)
)))
(declare-const AadlComponent_count Int)
(assert (= 4 AadlComponent_count))

(declare-const AadlComponentCategory (Array AadlComponent (Option ComponentCategory)))
  (assert (= (Some Process) (select AadlComponentCategory top_impl_Instance_src_process)))
  (assert (= (Some VirtualProcessor) (select AadlComponentCategory top_impl_Instance_vm_src_proc)))
  (assert (= (Some Process) (select AadlComponentCategory top_impl_Instance_dst_process)))
  (assert (= (Some VirtualProcessor) (select AadlComponentCategory top_impl_Instance_vm_dst_proc)))

(declare-const ProcessorBindings (Array AadlComponent (Option AadlComponent)))
  (assert (= (Some top_impl_Instance_vm_src_proc) (select ProcessorBindings top_impl_Instance_src_process)))
  (assert (= (Some top_impl_Instance_vm_dst_proc) (select ProcessorBindings top_impl_Instance_dst_process)))

(declare-const AadlDispatchProtocol (Array AadlComponent (Option DispatchProtocol)))
  (assert (= (Some Periodic) (select AadlDispatchProtocol top_impl_Instance_vm_src_proc)))
  (assert (= (Some Periodic) (select AadlDispatchProtocol top_impl_Instance_vm_dst_proc)))
(declare-const AadlDispatchProtocol_size Int)
(assert (= 2 AadlDispatchProtocol_size))

(declare-datatypes ((AadlPort 0)) ((
  (top_impl_Instance_src_process_write_port)
  (top_impl_Instance_dst_process_read_port))))
(declare-const AadlPort_count Int)
(assert (= 2 AadlPort_count))

(declare-const AadlPortComponent (Array AadlPort (Option AadlComponent)))
  (assert (= (Some top_impl_Instance_src_process) (select AadlPortComponent top_impl_Instance_src_process_write_port)))
  (assert (= (Some top_impl_Instance_dst_process) (select AadlPortComponent top_impl_Instance_dst_process_read_port)))
(declare-const AadlPortComponent_size Int)
(assert (= 2 AadlPortComponent_size))

(declare-const AadlFeatureCategory (Array AadlPort FeatureCategory))
  (assert (= DataPort (select AadlFeatureCategory top_impl_Instance_src_process_write_port)))
  (assert (= DataPort (select AadlFeatureCategory top_impl_Instance_dst_process_read_port)))
(declare-const AadlFeatureCategory_size Int)
(assert (= 2 AadlFeatureCategory_size))

(declare-const AadlPortDirection (Array AadlPort Direction))
  (assert (= Out (select AadlPortDirection top_impl_Instance_src_process_write_port)))
  (assert (= In (select AadlPortDirection top_impl_Instance_dst_process_read_port)))
(declare-const AadlPortDirection_size Int)
(assert (= 2 AadlPortDirection_size))

(define-fun AadlConnectionFlowTos ((p1 AadlPort) (p2 AadlPort)) Bool
  (or
    (and (= p1 top_impl_Instance_src_process_write_port) (= p2 top_impl_Instance_dst_process_read_port))
    false))
(declare-const AadlConnectionFlowsTos_count Int)
(assert (= 1 AadlConnectionFlowsTos_count))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                        ;;
;;                              CAmkES Model                              ;;
;;                                                                        ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-datatypes ((AccessType 0)) ((
  (R)
  (W)
  (RW))))

(declare-datatypes ((seL4ConnectorType 0)) ((
  (seL4GlobalAsynch)
  (seL4GlobalAsynchCallback)
  (seL4Notification)
  (seL4RPCCall)
  (seL4RPCDataport)
  (seL4SharedData)
  (seL4SharedDataWithCaps)
  (seL4SerialServer)
  (seL4TimeServer)
  (seL4VMDTBPassthrough)
  (CASE_AADL_EventDataport))))

(declare-datatypes ((CAmkESComponent 0)) ((
  (vmsrc_process)
  (fserv)
  (vmdst_process)
  (pacer))))
(declare-const CAmkESComponent_count Int)
(assert (= 4 CAmkESComponent_count))

(define-fun isPeriodicDispatcher ((_component CAmkESComponent)) Bool
  (and (= ModelSchedulingType PeriodicDispatching)
       false))

(define-fun isPacer ((_component CAmkESComponent)) Bool
  (and (= ModelSchedulingType Pacing)
       (= _component pacer)))

(define-fun isFileServer ((_component CAmkESComponent)) Bool
  (and ; TODO: list scenarios where a file server is expected
       (= _component fserv)))

(define-fun isTimeServer ((_component CAmkESComponent)) Bool
  (and ; TODO: list scenarios where a time server is expected
       false))

(define-fun isSerialServer ((_component CAmkESComponent)) Bool
  (and ; TODO: list scenarios where a serial server is expected
       false))

(declare-datatypes ((CAmkESPort 0)) ((
  (vmsrc_process_sb_write_port)
  (vmsrc_process_sb_pacer_period_queue)
  (vmsrc_process_notification_ready_connector)
  (vmsrc_process_fs)
  (vmsrc_process_batch)
  (vmsrc_process_guest_putchar)
  (vmsrc_process_serial_getchar)
  (vmsrc_process_recv)
  (vmsrc_process_send)
  (vmsrc_process_dtb_self)
  (vmsrc_process_restart_event)
  (vmsrc_process_notification_ready)
  (vmsrc_process_sb_pacer_period_notification)
  (vmsrc_process_dtb)
  (fserv_fs_ctrl)
  (vmdst_process_sb_read_port)
  (vmdst_process_sb_pacer_period_queue)
  (vmdst_process_notification_ready_connector)
  (vmdst_process_fs)
  (vmdst_process_batch)
  (vmdst_process_guest_putchar)
  (vmdst_process_serial_getchar)
  (vmdst_process_recv)
  (vmdst_process_send)
  (vmdst_process_dtb_self)
  (vmdst_process_restart_event)
  (vmdst_process_notification_ready)
  (vmdst_process_sb_pacer_period_notification)
  (vmdst_process_dtb)
  (pacer_period_to_vmsrc_process_queue)
  (pacer_period_to_vmdst_process_queue)
  (pacer_period_to_vmsrc_process_notification)
  (pacer_period_to_vmdst_process_notification)
  (pacer_tick)
  (pacer_tock))))
(declare-const CAmkESPort_count Int)
(assert (= 35 CAmkESPort_count))

(declare-const CAmkESAccessRestrictions (Array CAmkESPort AccessType))
  (assert (= RW (select CAmkESAccessRestrictions vmsrc_process_sb_write_port)))
  (assert (= R (select CAmkESAccessRestrictions vmdst_process_sb_read_port)))
  (assert (= W (select CAmkESAccessRestrictions pacer_period_to_vmsrc_process_queue)))
  (assert (= R (select CAmkESAccessRestrictions vmsrc_process_sb_pacer_period_queue)))
  (assert (= W (select CAmkESAccessRestrictions pacer_period_to_vmdst_process_queue)))
  (assert (= R (select CAmkESAccessRestrictions vmdst_process_sb_pacer_period_queue)))
(declare-const CAmkESAccessRestrictions_size Int)
(assert (= 6 CAmkESAccessRestrictions_size))

(declare-datatypes ((CAmkESConnection 0)) ((
  (conn1)
  (conn2)
  (conn3)
  (conn4)
  (conn5)
  (conn6)
  (conn7)
  (conn8)
  (conn9)
  (conn10)
  (conn11)
  (conn12))))
(declare-const CAmkESConnection_count Int)
(assert (= 12 CAmkESConnection_count))

(define-fun isSelfPacingConnection ((_conn CAmkESConnection)) Bool
  (and (= ModelSchedulingType SelfPacing)
       (or 
           false)))

(define-fun isPacingConnection ((_conn CAmkESConnection)) Bool
  (and (= ModelSchedulingType Pacing)
       (or (= _conn conn8)
           (= _conn conn9)
           (= _conn conn10)
           (= _conn conn11)
           (= _conn conn12)
           false)))

(define-fun isPeriodicDispatchingConnection ((_conn CAmkESConnection)) Bool
  (and (= ModelSchedulingType PeriodicDispatching)
       (or 
           false)))
(declare-const PeriodicDispatchingConnection_count Int)
(assert (= 0 PeriodicDispatchingConnection_count))

; non Aadl connection refinement connections required by a VM
(define-fun isVMAuxConnection ((_conn CAmkESConnection)) Bool
  (or (= _conn conn1)
      (= _conn conn2)
      (= _conn conn3)
      (= _conn conn4)
      (= _conn conn5)
      (= _conn conn6)
      false))

(declare-const CAmkESConnectionType (Array CAmkESConnection seL4ConnectorType))
  (assert (= seL4RPCDataport (select CAmkESConnectionType conn1)))
  (assert (= seL4GlobalAsynch (select CAmkESConnectionType conn2)))
  (assert (= seL4VMDTBPassthrough (select CAmkESConnectionType conn3)))
  (assert (= seL4RPCDataport (select CAmkESConnectionType conn4)))
  (assert (= seL4GlobalAsynch (select CAmkESConnectionType conn5)))
  (assert (= seL4VMDTBPassthrough (select CAmkESConnectionType conn6)))
  (assert (= seL4SharedDataWithCaps (select CAmkESConnectionType conn7)))
  (assert (= seL4Notification (select CAmkESConnectionType conn8)))
  (assert (= seL4GlobalAsynch (select CAmkESConnectionType conn9)))
  (assert (= seL4SharedDataWithCaps (select CAmkESConnectionType conn10)))
  (assert (= seL4GlobalAsynch (select CAmkESConnectionType conn11)))
  (assert (= seL4SharedDataWithCaps (select CAmkESConnectionType conn12)))
(declare-const CAmkESConnectionType_count Int)
(assert (= 12 CAmkESConnectionType_count))

(declare-const CAmkESPortComponent (Array CAmkESPort CAmkESComponent))
  (assert (= vmsrc_process (select CAmkESPortComponent vmsrc_process_sb_write_port)))
  (assert (= vmsrc_process (select CAmkESPortComponent vmsrc_process_sb_pacer_period_queue)))
  (assert (= vmsrc_process (select CAmkESPortComponent vmsrc_process_notification_ready_connector)))
  (assert (= vmsrc_process (select CAmkESPortComponent vmsrc_process_fs)))
  (assert (= vmsrc_process (select CAmkESPortComponent vmsrc_process_batch)))
  (assert (= vmsrc_process (select CAmkESPortComponent vmsrc_process_guest_putchar)))
  (assert (= vmsrc_process (select CAmkESPortComponent vmsrc_process_serial_getchar)))
  (assert (= vmsrc_process (select CAmkESPortComponent vmsrc_process_recv)))
  (assert (= vmsrc_process (select CAmkESPortComponent vmsrc_process_send)))
  (assert (= vmsrc_process (select CAmkESPortComponent vmsrc_process_dtb_self)))
  (assert (= vmsrc_process (select CAmkESPortComponent vmsrc_process_restart_event)))
  (assert (= vmsrc_process (select CAmkESPortComponent vmsrc_process_notification_ready)))
  (assert (= vmsrc_process (select CAmkESPortComponent vmsrc_process_sb_pacer_period_notification)))
  (assert (= vmsrc_process (select CAmkESPortComponent vmsrc_process_dtb)))
  (assert (= fserv (select CAmkESPortComponent fserv_fs_ctrl)))
  (assert (= vmdst_process (select CAmkESPortComponent vmdst_process_sb_read_port)))
  (assert (= vmdst_process (select CAmkESPortComponent vmdst_process_sb_pacer_period_queue)))
  (assert (= vmdst_process (select CAmkESPortComponent vmdst_process_notification_ready_connector)))
  (assert (= vmdst_process (select CAmkESPortComponent vmdst_process_fs)))
  (assert (= vmdst_process (select CAmkESPortComponent vmdst_process_batch)))
  (assert (= vmdst_process (select CAmkESPortComponent vmdst_process_guest_putchar)))
  (assert (= vmdst_process (select CAmkESPortComponent vmdst_process_serial_getchar)))
  (assert (= vmdst_process (select CAmkESPortComponent vmdst_process_recv)))
  (assert (= vmdst_process (select CAmkESPortComponent vmdst_process_send)))
  (assert (= vmdst_process (select CAmkESPortComponent vmdst_process_dtb_self)))
  (assert (= vmdst_process (select CAmkESPortComponent vmdst_process_restart_event)))
  (assert (= vmdst_process (select CAmkESPortComponent vmdst_process_notification_ready)))
  (assert (= vmdst_process (select CAmkESPortComponent vmdst_process_sb_pacer_period_notification)))
  (assert (= vmdst_process (select CAmkESPortComponent vmdst_process_dtb)))
  (assert (= pacer (select CAmkESPortComponent pacer_period_to_vmsrc_process_queue)))
  (assert (= pacer (select CAmkESPortComponent pacer_period_to_vmdst_process_queue)))
  (assert (= pacer (select CAmkESPortComponent pacer_period_to_vmsrc_process_notification)))
  (assert (= pacer (select CAmkESPortComponent pacer_period_to_vmdst_process_notification)))
  (assert (= pacer (select CAmkESPortComponent pacer_tick)))
  (assert (= pacer (select CAmkESPortComponent pacer_tock)))
(declare-const CAmkESPortComponent_size Int)
(assert (= 35 CAmkESPortComponent_size))

(define-fun CAmkESConnectionFlowTos ((_conn CAmkESConnection) (_p1 CAmkESPort) (_p2 CAmkESPort)) Bool
  (or
    (and (= _conn conn1) (= _p1 vmsrc_process_fs) (= _p2 fserv_fs_ctrl))
    (and (= _conn conn2) (= _p1 vmsrc_process_notification_ready_connector) (= _p2 vmsrc_process_notification_ready))
    (and (= _conn conn3) (= _p1 vmsrc_process_dtb_self) (= _p2 vmsrc_process_dtb))
    (and (= _conn conn4) (= _p1 vmdst_process_fs) (= _p2 fserv_fs_ctrl))
    (and (= _conn conn5) (= _p1 vmdst_process_notification_ready_connector) (= _p2 vmdst_process_notification_ready))
    (and (= _conn conn6) (= _p1 vmdst_process_dtb_self) (= _p2 vmdst_process_dtb))
    (and (= _conn conn7) (= _p1 vmsrc_process_sb_write_port) (= _p2 vmdst_process_sb_read_port))
    (and (= _conn conn8) (= _p1 pacer_tick) (= _p2 pacer_tock))
    (and (= _conn conn9) (= _p1 pacer_period_to_vmsrc_process_notification) (= _p2 vmsrc_process_sb_pacer_period_notification))
    (and (= _conn conn10) (= _p1 pacer_period_to_vmsrc_process_queue) (= _p2 vmsrc_process_sb_pacer_period_queue))
    (and (= _conn conn11) (= _p1 pacer_period_to_vmdst_process_notification) (= _p2 vmdst_process_sb_pacer_period_notification))
    (and (= _conn conn12) (= _p1 pacer_period_to_vmdst_process_queue) (= _p2 vmdst_process_sb_pacer_period_queue))
    false))
(declare-const CAmkESConnectionFlowTos_count Int)
(assert (= 12 CAmkESConnectionFlowTos_count))

(define-fun ComponentRefinement ((ac (Option AadlComponent)) (cc CAmkESComponent)) Bool
  (or
    (and (= ac (Some top_impl_Instance_src_process)) (= cc vmsrc_process))
    (and (= ac (Some top_impl_Instance_dst_process)) (= cc vmdst_process))
    false))
(declare-const ComponentRefinement_count Int)
(assert (= 2 ComponentRefinement_count))

(define-fun PortRefinement ((ap AadlPort) (cp CAmkESPort)) Bool
  (or
    (and (= ap top_impl_Instance_src_process_write_port) (= cp vmsrc_process_sb_write_port))
    (and (= ap top_impl_Instance_dst_process_read_port) (= cp vmdst_process_sb_read_port))
    false))
(declare-const PortRefinement_count Int)
(assert (= 2 PortRefinement_count))

(define-fun isVMAuxPort ((cp CAmkESPort)) Bool
  (exists ((cc CAmkESComponent))
    (and (= cc (select CAmkESPortComponent cp))
         (or (and (= cc vmsrc_process)
                  (or (= cp vmsrc_process_notification_ready_connector) (= cp vmsrc_process_fs) (= cp vmsrc_process_batch) (= cp vmsrc_process_guest_putchar) (= cp vmsrc_process_serial_getchar) (= cp vmsrc_process_recv) (= cp vmsrc_process_send) (= cp vmsrc_process_dtb_self) (= cp vmsrc_process_restart_event) (= cp vmsrc_process_notification_ready) (= cp vmsrc_process_dtb) false))
             (and (= cc vmdst_process)
                  (or (= cp vmdst_process_notification_ready_connector) (= cp vmdst_process_fs) (= cp vmdst_process_batch) (= cp vmdst_process_guest_putchar) (= cp vmdst_process_serial_getchar) (= cp vmdst_process_recv) (= cp vmdst_process_send) (= cp vmdst_process_dtb_self) (= cp vmdst_process_restart_event) (= cp vmdst_process_notification_ready) (= cp vmdst_process_dtb) false))
             false))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                        ;;
;;                             Proof Functions                            ;;
;;                                                                        ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun isVMComponent ((cc CAmkESComponent)) Bool
  (exists ((ap AadlComponent))
    (and (ComponentRefinement (Some ap) cc)                   ; cc refines ap
         (= (Some Process) (select AadlComponentCategory ap)) ; ap is a process
         (match (select ProcessorBindings ap) (
           ((Some x) (= (Some VirtualProcessor) (select AadlComponentCategory x))) ; ap is bound to virtual processor
           (None false))))))

(define-fun AadlFlowDirectionality () Bool
  (forall ((p1 AadlPort) (p2 AadlPort))
    (=> (AadlConnectionFlowTos p1 p2)
        (and (= Out (select AadlPortDirection p1)) (= In (select AadlPortDirection p2))))))

(define-fun AadlFlowNoSelfConnection () Bool
  (forall ((p1 AadlPort) (p2 AadlPort))
    (=> (AadlConnectionFlowTos p1 p2)
        (not (= p1 p2)))))

(define-fun AadlConnectedPortTypeMatch () Bool
  (forall ((src AadlPort) (dst AadlPort))
    (=> (AadlConnectionFlowTos src dst)
        (or (and (= AbstractFeature (select AadlFeatureCategory src)) (= AbstractFeature (select AadlFeatureCategory dst)))
            (and (= BusAccess (select AadlFeatureCategory src)) (= BusAccess (select AadlFeatureCategory dst)))
            (and (= DataAccess (select AadlFeatureCategory src)) (= DataAccess (select AadlFeatureCategory dst)))
            (and (= DataPort (select AadlFeatureCategory src)) (= DataPort (select AadlFeatureCategory dst)))
            (and (= EventPort (select AadlFeatureCategory src)) (= EventPort (select AadlFeatureCategory dst)))
            (and (= EventDataPort (select AadlFeatureCategory src)) (= EventDataPort (select AadlFeatureCategory dst)))
            (and (= FeatureGroup (select AadlFeatureCategory src)) (= FeatureGroup (select AadlFeatureCategory dst)))
            (and (= Parameter (select AadlFeatureCategory src)) (= Parameter (select AadlFeatureCategory dst)))
            (and (= SubprogramAccess (select AadlFeatureCategory src)) (= SubprogramAccess (select AadlFeatureCategory dst)))
            (and (= SubprogramAccessGroup (select AadlFeatureCategory src)) (= SubprogramAccessGroup (select AadlFeatureCategory dst)))
             false))))
(declare-const AadlConnectedPortTypeMatch_count Int)
(assert (= 10 AadlConnectedPortTypeMatch_count))

(define-fun AadlDispatchProtocolSpecified () Bool
  (forall ((_comp AadlComponent))
    (match (select AadlComponentCategory _comp) (
      ((Some _category_) (
        ; threads and virtual processors must have an assigned dispatch protocol, all others are 'don't care'
        match _category_ (
          (Thread (not (= (as None (Option DispatchProtocol)) (select AadlDispatchProtocol _comp))))
          (VirtualProcessor (not (= (as None (Option DispatchProtocol)) (select AadlDispatchProtocol _comp))))
          (_z_ true)
        )))
      (None false) ; sanity check: all AADL components must have an assigned component category
      ))))

(define-fun AadlAllPortsAssigned () Bool
  (forall ((_p AadlPort))
    (not (= (as None (Option AadlComponent)) (select AadlPortComponent _p)))))

(define-fun AADLWellFormedness () Bool
  (and
    (= AadlPort_count AadlPortComponent_size) ; all Aadl ports belong to an Aadl component
    AadlAllPortsAssigned
    AadlDispatchProtocolSpecified
    AadlFlowDirectionality
    AadlFlowNoSelfConnection
    AadlConnectedPortTypeMatch))


(define-fun CAmkESFlowNoSelfConnection () Bool
  (forall ((_conn CAmkESConnection) (_p1 CAmkESPort) (_p2 CAmkESPort))
    (=> (CAmkESConnectionFlowTos _conn _p1 _p2)
        (not (= _p1 _p2)))))

(define-fun CAmkESDataPortAccess () Bool
  (forall ((_conn CAmkESConnection) (_src CAmkESPort) (_dst CAmkESPort))
    (=> (CAmkESConnectionFlowTos _conn _src _dst)
        (and
             (=> (= seL4SharedData (select CAmkESConnectionType _conn))
                 (and (= W (select CAmkESAccessRestrictions _src))
                      (= R (select CAmkESAccessRestrictions _dst))))
             (=> (= seL4SharedDataWithCaps (select CAmkESConnectionType _conn))
                 (and (ite (isVMComponent (select CAmkESPortComponent _src))
                           (= RW (select CAmkESAccessRestrictions _src))
                           (= W (select CAmkESAccessRestrictions _src)))
                      (= R (select CAmkESAccessRestrictions _dst))))))))

(define-fun UniqueComponentRefinements () Bool
  (forall ((aadlComponent1 AadlComponent) (camkesComponent CAmkESComponent))
    (=> (ComponentRefinement (Some aadlComponent1) camkesComponent)
        (not (exists ((aadlComponent2 AadlComponent))
               (and (not (= aadlComponent1 aadlComponent2))
                    (ComponentRefinement (Some aadlComponent2) camkesComponent)))))))

(define-fun UniquePortRefinements () Bool
  (forall ((aadlPort1 AadlPort) (camkesPort CAmkESPort))
    (=> (PortRefinement aadlPort1 camkesPort)
        (not (exists ((aadlPort2 AadlPort))
               (and (not (= aadlPort1 aadlPort2))
                    (PortRefinement aadlPort2 camkesPort)))))))

(define-fun CAmkESWellFormedness () Bool
  (and
    (= CAmkESPort_count CAmkESPortComponent_size) ; all CAmkES ports belong to a CAmkES component
    CAmkESDataPortAccess
    CAmkESFlowNoSelfConnection))

; helper method: if either port belongs to a VM component then any data connection between the two of them
; must be seL4SharedDataWithCaps, seL4SharedData otherwise
(define-fun getExpectedDataConnectionType ((camkesSource CAmkESPort) (camkesDest CAmkESPort)) seL4ConnectorType
  (ite (or (isVMComponent (select CAmkESPortComponent camkesSource))
           (isVMComponent (select CAmkESPortComponent camkesDest))
           false)
       seL4SharedDataWithCaps
       seL4SharedData))

; helper method: if the destination port belongs to a VM component than any event connection between the two ports
; must be seL4GlobalAsynch, seL4Notification otherwise
(define-fun getExpectedEventConnectionType ((camkesSource CAmkESPort) (camkesDest CAmkESPort)) seL4ConnectorType
  (ite (isVMComponent (select CAmkESPortComponent camkesDest))
       seL4GlobalAsynch
       seL4Notification))

(define-fun SB_DataPortRefinement ((aadlSource AadlPort) (aadlDest AadlPort)) Bool
  (exists ((conn CAmkESConnection) (camkesSource CAmkESPort) (camkesDest CAmkESPort))
      (and (CAmkESConnectionFlowTos conn camkesSource camkesDest)
           (= (select CAmkESConnectionType conn) (getExpectedDataConnectionType camkesSource camkesDest)) ; actual connector type must match expected
           (PortRefinement aadlSource camkesSource)
           (PortRefinement aadlDest  camkesDest)
           (ComponentRefinement (select AadlPortComponent aadlSource) (select CAmkESPortComponent camkesSource))
           (ComponentRefinement (select AadlPortComponent aadlDest) (select CAmkESPortComponent camkesDest)))))

(define-fun SB_EventPortRefinement ((aadlSource AadlPort) (aadlDest AadlPort)) Bool
  (exists ((conn CAmkESConnection) (camkesSource CAmkESPort) (camkesDest CAmkESPort))
    (and
      (CAmkESConnectionFlowTos conn camkesSource camkesDest)
      (= (select CAmkESConnectionType conn) (getExpectedEventConnectionType camkesSource camkesDest)) ; actual connector type must match expected
      (PortRefinement aadlSource camkesSource)
      (PortRefinement aadlDest camkesDest)
      (ComponentRefinement (select AadlPortComponent aadlSource) (select CAmkESPortComponent camkesSource))
      (ComponentRefinement (select AadlPortComponent aadlDest) (select CAmkESPortComponent camkesDest)))))

(define-fun SB_Refinement ((aadlSource AadlPort) (aadlDest AadlPort)) Bool
  (and (or (= CodegenMode SeL4) (= CodegenMode SeL4_Only) false)
       (or
         (and
           (= DataPort (select AadlFeatureCategory aadlSource))
           (SB_DataPortRefinement aadlSource aadlDest)) ; payload
         (and
           (= EventPort (select AadlFeatureCategory aadlSource))
           (SB_DataPortRefinement aadlSource aadlDest)   ; event counter
           (SB_EventPortRefinement aadlSource aadlDest)) ; event
         (and
           (= EventDataPort (select AadlFeatureCategory aadlSource))
           (SB_DataPortRefinement aadlSource aadlDest)   ; payload
           (SB_EventPortRefinement aadlSource aadlDest)) ; event
         false)))

(define-fun ConnectionPreservation () Bool
  (forall ((aadlSource AadlPort) (aadlDest AadlPort))
    (=> (AadlConnectionFlowTos aadlSource aadlDest)
        (and (or (= CodegenMode SeL4) (= CodegenMode SeL4_Only) false)
             (SB_Refinement aadlSource aadlDest)))))


(define-fun isAadl_SB_ConnectionRefinement ((camkesSource CAmkESPort) (camkesDest CAmkESPort)) Bool
  (and (or (= CodegenMode SeL4) (= CodegenMode SeL4_Only) false)
       (exists ((aadlSource AadlPort) (aadlDest AadlPort))
         (and
           (PortRefinement aadlSource camkesSource)
           (PortRefinement aadlDest camkesDest)
           (ComponentRefinement (select AadlPortComponent aadlSource) (select CAmkESPortComponent camkesSource))
           (ComponentRefinement (select AadlPortComponent aadlDest) (select CAmkESPortComponent camkesDest))
           (AadlConnectionFlowTos aadlSource aadlDest)))))

(define-fun isCAmkESSchedulingConnection ((_conn CAmkESConnection)) Bool
  (or
    (isSelfPacingConnection _conn)
    (isPacingConnection _conn)
    (isPeriodicDispatchingConnection _conn)
    false))

(define-fun isVirtualMachineInducedConnection ((conn CAmkESConnection) (camkesSource CAmkESPort) (camkesDest CAmkESPort)) Bool
  (or
    (and (isVMAuxConnection conn)
         (or (isVMAuxPort camkesSource)
             (isVMAuxPort camkesDest)
             false))
    (and (isSerialServer (select CAmkESPortComponent camkesSource)) ; connection b/w serial and time server
         (isTimeServer (select CAmkESPortComponent camkesDest)))
    false))

(define-fun NoNewConnections () Bool
  (forall ((conn CAmkESConnection) (camkesSource CAmkESPort) (camkesDest CAmkESPort))
    (=> (CAmkESConnectionFlowTos conn camkesSource camkesDest)
      (or
        (isAadl_SB_ConnectionRefinement camkesSource camkesDest)
        (isCAmkESSchedulingConnection conn)
        (isVirtualMachineInducedConnection conn camkesSource camkesDest)
        false))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                        ;;
;;                              Proof                                     ;;
;;                                                                        ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(echo "RefinementProof: Shows that there is a model satisfying all the constraints (should be sat):")
(push)
(assert (and
  AADLWellFormedness
  CAmkESWellFormedness
  ConnectionPreservation
  UniqueComponentRefinements
  UniquePortRefinements
  NoNewConnections
))
(check-sat)
;(get-model)
(pop)

(echo "AADLWellFormedness: Proves that the generated AADL evidence is well-formed (should be unsat):")
(push)
(assert (not AADLWellFormedness))
(check-sat)
(pop)

(echo "CAmkESWellFormedness: Proves that the generated CAmkES evidence is well-formed (should be unsat):")
(push)
(assert (not CAmkESWellFormedness))
(check-sat)
(pop)

(echo "ConnectionPreservation: Proves that the generated CAmkES connections preserve AADL's (should be unsat):")
(push)
(assert (not ConnectionPreservation))
(check-sat)
(pop)

(echo "NoNewConnections: Proves that the generated CAmkES connections does not contain more than AADL's (should be unsat):")
(push)
(assert (not NoNewConnections))
(check-sat)
(pop)


(exit)