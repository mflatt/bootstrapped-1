static ptr copy(ptr p, seginfo *si)
{
  change = 1;
  check_triggers(si);
  {
    ptr new_p;
    IGEN tg = target_generation;
    {
      ITYPE t = TYPEBITS(p);
      if (t == type_typed_object)
      {
        ptr tf = TYPEFIELD(p);
        if (TYPEP(tf, mask_record, type_record))
        {
          /* Relocate to make sure we aren't using an oldspace descriptor
             that has been overwritten by a forwarding marker, but don't loop
             on tag-reflexive base descriptor */
          if (p != tf)
          {
            relocate(&RECORDINSTTYPE(p));
          }
          {
            ptr rtd = RECORDINSTTYPE(p);
            ISPC p_spc = ((is_counting_root(si, p))
                          ? space_count_impure
                          : ((((RECORDDESCPM(rtd)) == (FIX(1))) && ((RECORDDESCMPM(rtd)) == (FIX(0))))
                             ? space_data
                             : (((RECORDDESCPM(rtd)) == (FIX(-1)))
                                ? (BACKREFERENCES_ENABLED
                                   ? (((RECORDDESCMPM(rtd)) == (FIX(0)))
                                      ? space_pure_typed_object
                                      : space_impure_record)
                                   : (((RECORDDESCMPM(rtd)) == (FIX(0)))
                                      ? space_pure
                                      : space_impure))
                                : (((RECORDDESCMPM(rtd)) == (FIX(0)))
                                   ? space_pure_typed_object
                                   : space_impure_record))));
            {
              uptr len = UNFIX((RECORDDESCSIZE(rtd)));
              {
                uptr p_sz = size_record_inst(len);
                find_room(p_spc, tg, type_typed_object, p_sz, new_p);
                RECORDINSTTYPE(new_p) = ((tf == p)
                                         ? new_p
                                         : rtd);
                memcpy_aligned(&RECORDINSTIT(new_p, 0), &RECORDINSTIT(p, 0), len - ptr_bytes);
                if ((p_spc == space_pure) || ((p_spc == space_impure) || (p_spc == space_count_impure)))
                {
                  {
                    uptr ua_size = unaligned_size_record_inst(len);
                    if (p_sz != ua_size)
                    {
                      *(((ptr*)(TO_VOIDP((((uptr)(UNTYPE(new_p, type_typed_object))) + ua_size))))) = FIX(0);
                    }
                  }
                }
                if (S_G.enable_object_counts)
                {
                  {
                    ptr c_rtd = ((tf == p)
                                 ? new_p
                                 : rtd);
                    ptr counts = RECORDDESCCOUNTS(c_rtd);
                    if (counts == Sfalse)
                    {
                      {
                        IGEN grtd = GENERATION(c_rtd);
                        (S_G.countof[grtd])[countof_rtd_counts] += 1;
                        find_room(space_data, grtd, type_typed_object, size_rtd_counts, counts);
                        RTDCOUNTSTYPE(counts) = type_rtd_counts;
                        RTDCOUNTSTIMESTAMP(counts) = S_G.gctimestamp[0];
                        {
                          IGEN g = 0;
                          while (g <= static_generation)
                          {
                            RTDCOUNTSIT(counts, g) = 0;
                            g += 1;
                          }
                        }
                        RECORDDESCCOUNTS(c_rtd) = counts;
                        S_G.rtds_with_counts[grtd] = S_cons_in(((grtd <= max_copied_generation) ? space_new : space_impure), ((grtd <= max_copied_generation) ? 0 : grtd), c_rtd, S_G.rtds_with_counts[grtd]);
                        (S_G.countof[grtd])[countof_pair] += 1;
                      }
                    }
                    else
                    {
                      relocate(&counts);
                      RECORDDESCCOUNTS(c_rtd) = counts;
                      if ((RTDCOUNTSTIMESTAMP(counts)) != (S_G.gctimestamp[0]))
                      {
                        S_fixup_counts(counts);
                      }
                    }
                    RTDCOUNTSIT(counts, tg) = (RTDCOUNTSIT(counts, tg)) + 1;
                  }
                }
                if (p_spc == space_count_impure)
                {
                  count_root_bytes += p_sz;
                }
                S_G.countof[tg][countof_record] += 1;
                S_G.bytesof[tg][countof_record] += p_sz;
              }
            }
          }
        }
        else if (TYPEP(tf, mask_vector, type_vector))
        {
          ISPC p_spc = ((((uptr)tf) & vector_immutable_flag)
                        ? (BACKREFERENCES_ENABLED
                           ? space_pure_typed_object
                           : space_pure)
                        : (BACKREFERENCES_ENABLED
                           ? space_impure_typed_object
                           : space_impure));
          {
            uptr len = Svector_length(p);
            {
              uptr p_sz = size_vector(len);
              find_room(p_spc, tg, type_typed_object, p_sz, new_p);
              VECTTYPE(new_p) = (uptr)tf;
              memcpy_aligned(&INITVECTIT(new_p, 0), &INITVECTIT(p, 0), ptr_bytes * len);
              if ((len & 1) == 0)
              {
                INITVECTIT(new_p, len) = FIX(0);
              }
              S_G.countof[tg][countof_vector] += 1;
              S_G.bytesof[tg][countof_vector] += p_sz;
            }
          }
        }
        else if (TYPEP(tf, mask_stencil_vector, type_stencil_vector))
        {
          ISPC p_spc = (BACKREFERENCES_ENABLED
                        ? space_impure_typed_object
                        : space_impure);
          {
            uptr len = Sstencil_vector_length(p);
            {
              uptr p_sz = size_stencil_vector(len);
              find_room(p_spc, tg, type_typed_object, p_sz, new_p);
              STENVECTTYPE(new_p) = (uptr)tf;
              memcpy_aligned(&INITSTENVECTIT(new_p, 0), &INITSTENVECTIT(p, 0), ptr_bytes * len);
              if ((len & 1) == 0)
              {
                INITSTENVECTIT(new_p, len) = FIX(0);
              }
              S_G.countof[tg][countof_stencil_vector] += 1;
              S_G.bytesof[tg][countof_stencil_vector] += p_sz;
            }
          }
        }
        else if (TYPEP(tf, mask_string, type_string))
        {
          ISPC p_spc = space_data;
          {
            uptr sz = size_string((Sstring_length(p)));
            {
              uptr p_sz = sz;
              find_room(p_spc, tg, type_typed_object, p_sz, new_p);
              memcpy_aligned(&STRTYPE(new_p), &STRTYPE(p), sz);
              S_G.countof[tg][countof_string] += 1;
              S_G.bytesof[tg][countof_string] += p_sz;
            }
          }
        }
        else if (TYPEP(tf, mask_fxvector, type_fxvector))
        {
          ISPC p_spc = space_data;
          {
            uptr sz = size_fxvector((Sfxvector_length(p)));
            {
              uptr p_sz = sz;
              find_room(p_spc, tg, type_typed_object, p_sz, new_p);
              memcpy_aligned(&FXVECTOR_TYPE(new_p), &FXVECTOR_TYPE(p), sz);
              S_G.countof[tg][countof_fxvector] += 1;
              S_G.bytesof[tg][countof_fxvector] += p_sz;
            }
          }
        }
        else if (TYPEP(tf, mask_bytevector, type_bytevector))
        {
          ISPC p_spc = space_data;
          {
            uptr sz = size_bytevector((Sbytevector_length(p)));
            {
              uptr p_sz = sz;
              find_room(p_spc, tg, type_typed_object, p_sz, new_p);
              memcpy_aligned(&BYTEVECTOR_TYPE(new_p), &BYTEVECTOR_TYPE(p), sz);
              S_G.countof[tg][countof_bytevector] += 1;
              S_G.bytesof[tg][countof_bytevector] += p_sz;
            }
          }
        }
        else if ((iptr)tf == type_tlc)
        {
          ISPC p_spc = (BACKREFERENCES_ENABLED
                        ? space_impure_typed_object
                        : space_impure);
          {
            uptr p_sz = size_tlc;
            find_room(p_spc, tg, type_typed_object, p_sz, new_p);
            TLCTYPE(new_p) = type_tlc;
            INITTLCHT(new_p) = INITTLCHT(p);
            {
              ptr next = INITTLCNEXT(p);
              {
                ptr keyval = INITTLCKEYVAL(p);
                INITTLCNEXT(new_p) = next;
                INITTLCKEYVAL(new_p) = keyval;
                if ((next != Sfalse) && (OLDSPACE(keyval)))
                {
                  tlcs_to_rehash = S_cons_in(space_new, 0, new_p, tlcs_to_rehash);
                }
                S_G.countof[tg][countof_tlc] += 1;
              }
            }
          }
        }
        else if (TYPEP(tf, mask_box, type_box))
        {
          ISPC p_spc = (((BOXTYPE(p)) == type_immutable_box)
                        ? (BACKREFERENCES_ENABLED
                           ? space_pure_typed_object
                           : space_pure)
                        : (BACKREFERENCES_ENABLED
                           ? space_impure_typed_object
                           : space_impure));
          {
            uptr p_sz = size_box;
            find_room(p_spc, tg, type_typed_object, p_sz, new_p);
            BOXTYPE(new_p) = (uptr)tf;
            INITBOXREF(new_p) = INITBOXREF(p);
            S_G.countof[tg][countof_box] += 1;
          }
        }
        else if ((iptr)tf == type_ratnum)
        {
          ISPC p_spc = space_data;
          {
            uptr p_sz = size_ratnum;
            find_room(p_spc, tg, type_typed_object, p_sz, new_p);
            RATTYPE(new_p) = type_ratnum;
            {
              ptr tmp_p = RATNUM(p);
              relocate(&tmp_p);
              RATNUM(new_p) = tmp_p;
            }
            {
              ptr tmp_p = RATDEN(p);
              relocate(&tmp_p);
              RATDEN(new_p) = tmp_p;
            }
            S_G.countof[tg][countof_ratnum] += 1;
          }
        }
        else if ((iptr)tf == type_exactnum)
        {
          ISPC p_spc = space_data;
          {
            uptr p_sz = size_exactnum;
            find_room(p_spc, tg, type_typed_object, p_sz, new_p);
            EXACTNUM_TYPE(new_p) = type_exactnum;
            {
              ptr tmp_p = EXACTNUM_REAL_PART(p);
              relocate(&tmp_p);
              EXACTNUM_REAL_PART(new_p) = tmp_p;
            }
            {
              ptr tmp_p = EXACTNUM_IMAG_PART(p);
              relocate(&tmp_p);
              EXACTNUM_IMAG_PART(new_p) = tmp_p;
            }
            S_G.countof[tg][countof_exactnum] += 1;
          }
        }
        else if ((iptr)tf == type_inexactnum)
        {
          ISPC p_spc = space_data;
          {
            uptr p_sz = size_inexactnum;
            find_room(p_spc, tg, type_typed_object, p_sz, new_p);
            INEXACTNUM_TYPE(new_p) = type_inexactnum;
            {
              ptr tmp_p = TYPE(TO_PTR(&INEXACTNUM_REAL_PART(p)), type_flonum);
              if (flonum_is_forwarded_p(tmp_p, si))
                INEXACTNUM_REAL_PART(new_p) = FLODAT(FLONUM_FWDADDRESS(tmp_p));
              else
                INEXACTNUM_REAL_PART(new_p) = INEXACTNUM_REAL_PART(p);
            }
            {
              ptr tmp_p = TYPE(TO_PTR(&INEXACTNUM_IMAG_PART(p)), type_flonum);
              if (flonum_is_forwarded_p(tmp_p, si))
                INEXACTNUM_IMAG_PART(new_p) = FLODAT(FLONUM_FWDADDRESS(tmp_p));
              else
                INEXACTNUM_IMAG_PART(new_p) = INEXACTNUM_IMAG_PART(p);
            }
            S_G.countof[tg][countof_inexactnum] += 1;
          }
        }
        else if (TYPEP(tf, mask_bignum, type_bignum))
        {
          ISPC p_spc = space_data;
          {
            uptr sz = size_bignum((BIGLEN(p)));
            {
              uptr p_sz = sz;
              find_room(p_spc, tg, type_typed_object, p_sz, new_p);
              memcpy_aligned(&BIGTYPE(new_p), &BIGTYPE(p), sz);
              S_G.countof[tg][countof_bignum] += 1;
              S_G.bytesof[tg][countof_bignum] += p_sz;
            }
          }
        }
        else if (TYPEP(tf, mask_port, type_port))
        {
          ISPC p_spc = space_port;
          {
            uptr p_sz = size_port;
            find_room(p_spc, tg, type_typed_object, p_sz, new_p);
            PORTTYPE(new_p) = (uptr)tf;
            PORTHANDLER(new_p) = PORTHANDLER(p);
            PORTOCNT(new_p) = PORTOCNT(p);
            PORTICNT(new_p) = PORTICNT(p);
            PORTOLAST(new_p) = PORTOLAST(p);
            PORTOBUF(new_p) = PORTOBUF(p);
            PORTILAST(new_p) = PORTILAST(p);
            PORTIBUF(new_p) = PORTIBUF(p);
            PORTINFO(new_p) = PORTINFO(p);
            PORTNAME(new_p) = PORTNAME(p);
            S_G.countof[tg][countof_port] += 1;
          }
        }
        else if (TYPEP(tf, mask_code, type_code))
        {
          ISPC p_spc = space_code;
          {
            uptr len = CODELEN(p);
            {
              uptr p_sz = size_code(len);
              find_room(p_spc, tg, type_typed_object, p_sz, new_p);
              CODETYPE(new_p) = (uptr)tf;
              CODELEN(new_p) = CODELEN(p);
              CODERELOC(new_p) = CODERELOC(p);
              CODENAME(new_p) = CODENAME(p);
              CODEARITYMASK(new_p) = CODEARITYMASK(p);
              CODEFREE(new_p) = CODEFREE(p);
              CODEINFO(new_p) = CODEINFO(p);
              CODEPINFOS(new_p) = CODEPINFOS(p);
              memcpy_aligned(&CODEIT(new_p, 0), &CODEIT(p, 0), len);
              S_G.countof[tg][countof_code] += 1;
              S_G.bytesof[tg][countof_code] += p_sz;
            }
          }
        }
        else if ((iptr)tf == type_thread)
        {
          ISPC p_spc = ((is_counting_root(si, p))
                        ? space_count_pure
                        : space_pure_typed_object);
          {
            uptr p_sz = size_thread;
            find_room(p_spc, tg, type_typed_object, p_sz, new_p);
            THREADTYPE(new_p) = type_thread;
            THREADTC(new_p) = THREADTC(p);
            S_G.countof[tg][countof_thread] += 1;
          }
        }
        else if ((iptr)tf == type_rtd_counts)
        {
          ISPC p_spc = space_data;
          {
            uptr p_sz = size_rtd_counts;
            find_room(p_spc, tg, type_typed_object, p_sz, new_p);
            memcpy_aligned(&RTDCOUNTSTYPE(new_p), &RTDCOUNTSTYPE(p), size_rtd_counts);
            S_G.countof[tg][countof_rtd_counts] += 1;
          }
        }
        else if ((iptr)tf == type_phantom)
        {
          ISPC p_spc = space_data;
          {
            uptr p_sz = size_phantom;
            find_room(p_spc, tg, type_typed_object, p_sz, new_p);
            PHANTOMTYPE(new_p) = type_phantom;
            PHANTOMLEN(new_p) = PHANTOMLEN(p);
            S_G.countof[tg][countof_phantom] += 1;
            (S_G.bytesof[tg])[countof_phantom] += PHANTOMLEN(p);
          }
        }
        else
        {
          S_error_abort("copy: illegal typed object type");
        }
      }
      else if (t == type_pair)
      {
        {
          ISPC p_at_spc = si->space;
          if (p_at_spc == space_ephemeron)
          {
            ISPC p_spc = space_ephemeron;
            {
              uptr p_sz = size_ephemeron;
              find_room(p_spc, tg, type_pair, p_sz, new_p);
              INITCAR(new_p) = INITCAR(p);
              INITCDR(new_p) = INITCDR(p);
              INITEPHEMERONPREVREF(new_p) = 0;
              INITEPHEMERONNEXT(new_p) = 0;
              S_G.countof[tg][countof_ephemeron] += 1;
            }
          }
          else if (p_at_spc == space_weakpair)
          {
            ISPC p_spc = space_weakpair;
            {
              ptr cdr_p = Scdr(p);
              {
                seginfo* qsi = NULL;
                if ((cdr_p != p) && (((TYPEBITS(cdr_p)) == type_pair) && (((qsi = (MaybeSegInfo((ptr_get_segment(cdr_p))))) != NULL) && ((qsi -> old_space) && (((qsi -> space) == (si -> space)) && (((FWDMARKER(cdr_p)) != forward_marker) && ((!(qsi -> use_marks)) && (!(qsi -> marked_mask)))))))))
                {
                  check_triggers(qsi);
                  {
                    uptr p_sz = 2 * (size_pair);
                    find_room(p_spc, tg, type_pair, p_sz, new_p);
                    {
                      ptr new_cdr_p = (ptr)(((uptr)new_p) + size_pair);
                      INITCAR(new_p) = INITCAR(p);
                      INITCDR(new_p) = new_cdr_p;
                      INITCAR(new_cdr_p) = INITCAR(cdr_p);
                      INITCDR(new_cdr_p) = INITCDR(cdr_p);
                      FWDMARKER(cdr_p) = forward_marker;
                      FWDADDRESS(cdr_p) = new_cdr_p;
                      ADD_BACKREFERENCE_FROM(new_cdr_p, new_p);
                      S_G.countof[tg][countof_weakpair] += 2;
                    }
                  }
                }
                else
                {
                  uptr p_sz = size_pair;
                  find_room(p_spc, tg, type_pair, p_sz, new_p);
                  INITCAR(new_p) = INITCAR(p);
                  INITCDR(new_p) = INITCDR(p);
                  S_G.countof[tg][countof_weakpair] += 1;
                }
              }
            }
          }
          else
          {
            ISPC p_spc = space_impure;
            {
              ptr cdr_p = Scdr(p);
              {
                seginfo* qsi = NULL;
                if ((cdr_p != p) && (((TYPEBITS(cdr_p)) == type_pair) && (((qsi = (MaybeSegInfo((ptr_get_segment(cdr_p))))) != NULL) && ((qsi -> old_space) && (((qsi -> space) == (si -> space)) && (((FWDMARKER(cdr_p)) != forward_marker) && ((!(qsi -> use_marks)) && (!(qsi -> marked_mask)))))))))
                {
                  check_triggers(qsi);
                  {
                    uptr p_sz = 2 * (size_pair);
                    find_room(p_spc, tg, type_pair, p_sz, new_p);
                    {
                      ptr new_cdr_p = (ptr)(((uptr)new_p) + size_pair);
                      INITCAR(new_p) = INITCAR(p);
                      INITCDR(new_p) = new_cdr_p;
                      INITCAR(new_cdr_p) = INITCAR(cdr_p);
                      INITCDR(new_cdr_p) = INITCDR(cdr_p);
                      FWDMARKER(cdr_p) = forward_marker;
                      FWDADDRESS(cdr_p) = new_cdr_p;
                      ADD_BACKREFERENCE_FROM(new_cdr_p, new_p);
                      S_G.countof[tg][countof_pair] += 2;
                    }
                  }
                }
                else
                {
                  uptr p_sz = size_pair;
                  find_room(p_spc, tg, type_pair, p_sz, new_p);
                  INITCAR(new_p) = INITCAR(p);
                  INITCDR(new_p) = INITCDR(p);
                  S_G.countof[tg][countof_pair] += 1;
                }
              }
            }
          }
        }
      }
      else if (t == type_closure)
      {
        ptr code = CLOSCODE(p);
        relocate(&code);
        if ((CODETYPE(code)) & (code_flag_continuation << code_flags_offset))
        {
          ISPC p_spc = ((is_counting_root(si, p))
                        ? space_count_pure
                        : space_continuation);
          {
            uptr p_sz = size_continuation;
            find_room(p_spc, tg, type_closure, p_sz, new_p);
            SETCLOSCODE(new_p, code);
            if ((CONTLENGTH(p)) == opportunistic_1_shot_flag)
            {
              CONTLENGTH(new_p) = CONTCLENGTH(p);
              conts_to_promote = S_cons_in(space_new, 0, new_p, conts_to_promote);
            }
            else
            {
              CONTLENGTH(new_p) = CONTLENGTH(p);
            }
            CONTCLENGTH(new_p) = CONTCLENGTH(p);
            CONTWINDERS(new_p) = CONTWINDERS(p);
            CONTATTACHMENTS(new_p) = CONTATTACHMENTS(p);
            if ((CONTLENGTH(p)) == scaled_shot_1_shot_flag)
            {
            }
            else
            {
              CONTLINK(new_p) = CONTLINK(p);
              CONTRET(new_p) = CONTRET(p);
              CONTSTACK(new_p) = CONTSTACK(p);
            }
            S_G.countof[tg][countof_continuation] += 1;
          }
        }
        else
        {
          ISPC p_spc = ((is_counting_root(si, p))
                        ? space_count_impure
                        : (BACKREFERENCES_ENABLED
                           ? space_closure
                           : (((CODETYPE(code)) & (code_flag_mutable_closure << code_flags_offset))
                              ? space_impure
                              : space_pure)));
          {
            uptr len = CODEFREE(code);
            {
              uptr p_sz = size_closure(len);
              find_room(p_spc, tg, type_closure, p_sz, new_p);
              SETCLOSCODE(new_p, code);
              memcpy_aligned(&CLOSIT(new_p, 0), &CLOSIT(p, 0), ptr_bytes * len);
              if ((len & 1) == 0)
              {
                CLOSIT(new_p, len) = FIX(0);
              }
              S_G.countof[tg][countof_closure] += 1;
              S_G.bytesof[tg][countof_closure] += p_sz;
            }
          }
        }
      }
      else if (t == type_symbol)
      {
        ISPC p_spc = space_symbol;
        {
          uptr p_sz = size_symbol;
          find_room(p_spc, tg, type_symbol, p_sz, new_p);
          INITSYMVAL(new_p) = INITSYMVAL(p);
          INITSYMPVAL(new_p) = INITSYMPVAL(p);
          INITSYMPLIST(new_p) = INITSYMPLIST(p);
          INITSYMNAME(new_p) = INITSYMNAME(p);
          INITSYMSPLIST(new_p) = INITSYMSPLIST(p);
          INITSYMHASH(new_p) = INITSYMHASH(p);
          S_G.countof[tg][countof_symbol] += 1;
        }
      }
      else if (t == type_flonum)
      {
        ISPC p_spc = space_data;
        {
          uptr p_sz = size_flonum;
          find_room(p_spc, tg, type_flonum, p_sz, new_p);
          FLODAT(new_p) = FLODAT(p);
          flonum_set_forwarded(p, si);
          FLONUM_FWDADDRESS(p) = new_p;
          S_G.countof[tg][countof_flonum] += 1;
          return new_p;
        }
      }
      else
      {
        S_error_abort("copy: illegal type");
      }
    }
    FWDMARKER(p) = forward_marker;
    FWDADDRESS(p) = new_p;
    ADD_BACKREFERENCE(p)
    return new_p;
  }
}

static void sweep(ptr tc_in, ptr p)
{
  PUSH_BACKREFERENCE(p)
  {
    ITYPE t = TYPEBITS(p);
    if (t == type_typed_object)
    {
      ptr tf = TYPEFIELD(p);
      if (TYPEP(tf, mask_record, type_record))
      {
        /* Relocate to make sure we aren't using an oldspace descriptor
           that has been overwritten by a forwarding marker, but don't loop
           on tag-reflexive base descriptor */
        if (p != tf)
        {
          relocate(&RECORDINSTTYPE(p));
        }
        {
          ptr rtd = RECORDINSTTYPE(p);
          {
            uptr len = UNFIX((RECORDDESCSIZE(rtd)));
            {
              ptr num = RECORDDESCPM(rtd);
              ptr* pp = &(RECORDINSTIT(p, 0));
              if (Sfixnump(num))
              {
                {
                  uptr mask = ((uptr)(UNFIX(num))) >> 1;
                  if (mask == (((uptr)-1) >> 1))
                  {
                    {
                      ptr* ppend = ((ptr*)(TO_VOIDP((((uptr)(TO_PTR(pp))) + len)))) - 1;
                      while (pp < ppend)
                      {
                        relocate(&(*(pp)));
                        pp += 1;
                      }
                    }
                  }
                  else
                  {
                    while (mask != 0)
                    {
                      if (mask & 1)
                      {
                        relocate(&(*(pp)));
                      }
                      mask >>= 1;
                      pp += 1;
                    }
                  }
                }
              }
              else
              {
                relocate(&(RECORDDESCPM(rtd)));
                num = RECORDDESCPM(rtd);
                {
                  iptr index = (BIGLEN(num)) - 1;
                  bigit mask = (BIGIT(num, index)) >> 1;
                  INT bits = bigit_bits - 1;
                  while (1)
                  {
                    do
                    {
                      if (mask & 1)
                      {
                        relocate(&(*(pp)));
                      }
                      mask >>= 1;
                      pp += 1;
                      bits -= 1;
                    }
                    while (bits > 0);
                    if (index == 0)
                    {
                      break;
                    }
                    index -= 1;
                    mask = BIGIT(num, index);
                    bits = bigit_bits;
                  }
                }
              }
            }
          }
        }
      }
      else if (TYPEP(tf, mask_vector, type_vector))
      {
        uptr len = Svector_length(p);
        {
          uptr idx, p_len = len;
          ptr *p_p = &INITVECTIT(p, 0);
          for (idx = 0; idx < p_len; idx++)
          {
            relocate(&(p_p[idx]));
          }
        }
      }
      else if (TYPEP(tf, mask_stencil_vector, type_stencil_vector))
      {
        uptr len = Sstencil_vector_length(p);
        {
          uptr idx, p_len = len;
          ptr *p_p = &INITSTENVECTIT(p, 0);
          for (idx = 0; idx < p_len; idx++)
          {
            relocate(&(p_p[idx]));
          }
        }
      }
      else if (TYPEP(tf, mask_string, type_string))
      {
      }
      else if (TYPEP(tf, mask_fxvector, type_fxvector))
      {
      }
      else if (TYPEP(tf, mask_bytevector, type_bytevector))
      {
      }
      else if ((iptr)tf == type_tlc)
      {
        relocate(&INITTLCHT(p));
        relocate(&INITTLCKEYVAL(p));
        relocate(&INITTLCNEXT(p));
      }
      else if (TYPEP(tf, mask_box, type_box))
      {
        relocate(&INITBOXREF(p));
      }
      else if ((iptr)tf == type_ratnum)
      {
        relocate(&RATNUM(p));
        relocate(&RATDEN(p));
      }
      else if ((iptr)tf == type_exactnum)
      {
        relocate(&EXACTNUM_REAL_PART(p));
        relocate(&EXACTNUM_IMAG_PART(p));
      }
      else if ((iptr)tf == type_inexactnum)
      {
      }
      else if (TYPEP(tf, mask_bignum, type_bignum))
      {
      }
      else if (TYPEP(tf, mask_port, type_port))
      {
        relocate(&PORTHANDLER(p));
        if (((uptr)tf) & PORT_FLAG_OUTPUT)
        {
          iptr n = ((iptr)(PORTOLAST(p))) - ((iptr)(PORTOBUF(p)));
          relocate(&PORTOBUF(p));
          PORTOLAST(p) = (ptr)(((iptr)(PORTOBUF(p))) + n);
        }
        if (((uptr)tf) & PORT_FLAG_INPUT)
        {
          iptr n = ((iptr)(PORTILAST(p))) - ((iptr)(PORTIBUF(p)));
          relocate(&PORTIBUF(p));
          PORTILAST(p) = (ptr)(((iptr)(PORTIBUF(p))) + n);
        }
        relocate(&PORTINFO(p));
        relocate(&PORTNAME(p));
      }
      else if (TYPEP(tf, mask_code, type_code))
      {
        relocate(&CODENAME(p));
        relocate(&CODEARITYMASK(p));
        relocate(&CODEINFO(p));
        relocate(&CODEPINFOS(p));
        {
          ptr t = CODERELOC(p);
          {
            iptr m = RELOCSIZE(t);
            {
              ptr oldco = RELOCCODE(t);
              {
                iptr a = 0;
                {
                  iptr n = 0;
                  while (n < m)
                  {
                    {
                      uptr entry = RELOCIT(t, n);
                      uptr item_off = 0;
                      uptr code_off = 0;
                      n = n + 1;
                      if (RELOC_EXTENDED_FORMAT(entry))
                      {
                        item_off = RELOCIT(t, n);
                        n = n + 1;
                        code_off = RELOCIT(t, n);
                        n = n + 1;
                      }
                      else
                      {
                        item_off = RELOC_ITEM_OFFSET(entry);
                        code_off = RELOC_CODE_OFFSET(entry);
                      }
                      a = a + code_off;
                      {
                        ptr obj = S_get_code_obj(RELOC_TYPE(entry), oldco, a, item_off);
                        relocate(&obj);
                        S_set_code_obj("gc", RELOC_TYPE(entry), p, a, obj, item_off);
                      }
                    }
                  }
                  if ((target_generation == static_generation) && ((!S_G.retain_static_relocation) && (0 == ((CODETYPE(p)) & (code_flag_template << code_flags_offset)))))
                  {
                    CODERELOC(p) = (ptr)0;
                  }
                  else
                  {
                    {
                      seginfo* t_si = SegInfo((ptr_get_segment(t)));
                      if (t_si -> old_space)
                      {
                        n = size_reloc_table((RELOCSIZE(t)));
                        S_G.countof[target_generation][countof_relocation_table] += 1;
                        S_G.bytesof[target_generation][countof_relocation_table] += n;
                        if (t_si -> use_marks)
                        {
                          mark_typemod_data_object(t, n, t_si);
                        }
                        else
                        {
                          {
                            ptr oldt = t;
                            find_room(space_data, target_generation, typemod, n, t);
                            memcpy_aligned(TO_VOIDP(t), TO_VOIDP(oldt), n);
                          }
                        }
                      }
                    }
                    RELOCCODE(t) = p;
                    CODERELOC(p) = t;
                  }
                  S_record_code_mod(tc_in, (uptr)(TO_PTR((&(CODEIT(p, 0))))), (uptr)(CODELEN(p)));
                }
              }
            }
          }
        }
      }
      else if ((iptr)tf == type_thread)
      {
        {
          ptr tc = (ptr)(THREADTC(p));
          if (tc != ((ptr)0))
          {
            {
              ptr old_stack = SCHEMESTACK(tc);
              if (OLDSPACE(old_stack))
              {
                {
                  iptr clength = ((uptr)(SFP(tc))) - ((uptr)old_stack);
                  SCHEMESTACK(tc) = copy_stack(old_stack, &(SCHEMESTACKSIZE(tc)), clength + (sizeof(ptr)));
                  S_G.countof[target_generation][countof_stack] += 1;
                  S_G.bytesof[target_generation][countof_stack] += SCHEMESTACKSIZE(tc);
                  SFP(tc) = (ptr)(((uptr)(SCHEMESTACK(tc))) + clength);
                  ESP(tc) = (ptr)((((uptr)(SCHEMESTACK(tc))) + (SCHEMESTACKSIZE(tc))) - stack_slop);
                }
              }
            }
            STACKCACHE(tc) = Snil;
            relocate(&(CCHAIN(tc)));
            relocate(&(STACKLINK(tc)));
            relocate(&(WINDERS(tc)));
            relocate(&(ATTACHMENTS(tc)));
            CACHEDFRAME(tc) = Sfalse;
            {
              ptr xcp = FRAME(tc, 0);
              {
                iptr co = (ENTRYOFFSET(xcp)) + (((uptr)xcp) - ((uptr)(TO_PTR((ENTRYOFFSETADDR(xcp))))));
                {
                  ptr c_p = (ptr)(((uptr)xcp) - co);
                  {
                    seginfo* x_si = SegInfo((ptr_get_segment(c_p)));
                    if (x_si -> old_space)
                    {
                      relocate_code(c_p, x_si);
                      FRAME(tc, 0) = (ptr)(((uptr)c_p) + co);
                    }
                    {
                      uptr base = (uptr)(SCHEMESTACK(tc));
                      {
                        uptr fp = (uptr)(SFP(tc));
                        {
                          uptr ret = (uptr)(FRAME(tc, 0));
                          while (fp != base)
                          {
                            if (fp < base)
                            {
                              S_error_abort("sweep_stack(gc): malformed stack");
                            }
                            fp = fp - (ENTRYFRAMESIZE(ret));
                            {
                              ptr* pp = (ptr*)(TO_VOIDP(fp));
                              iptr oldret = ret;
                              ret = (iptr)(*(pp));
                              {
                                ptr xcp = *(pp);
                                {
                                  iptr co = (ENTRYOFFSET(xcp)) + (((uptr)xcp) - ((uptr)(TO_PTR((ENTRYOFFSETADDR(xcp))))));
                                  {
                                    ptr c_p = (ptr)(((uptr)xcp) - co);
                                    {
                                      seginfo* x_si = SegInfo((ptr_get_segment(c_p)));
                                      if (x_si -> old_space)
                                      {
                                        relocate_code(c_p, x_si);
                                        *(pp) = (ptr)(((uptr)c_p) + co);
                                      }
                                      {
                                        ptr num = ENTRYLIVEMASK(oldret);
                                        if (Sfixnump(num))
                                        {
                                          {
                                            uptr mask = UNFIX(num);
                                            while (mask != 0)
                                            {
                                              pp += 1;
                                              if (mask & 1)
                                              {
                                                relocate(&(*(pp)));
                                              }
                                              mask >>= 1;
                                            }
                                          }
                                        }
                                        else
                                        {
                                          relocate(&(*((ENTRYNONCOMPACTLIVEMASKADDR(oldret)))));
                                          {
                                            ptr num = ENTRYLIVEMASK(oldret);
                                            iptr index = BIGLEN(num);
                                            while (index != 0)
                                            {
                                              index -= 1;
                                              {
                                                INT bits = bigit_bits;
                                                bigit mask = BIGIT(num, index);
                                                while (bits > 0)
                                                {
                                                  bits -= 1;
                                                  pp += 1;
                                                  if (mask & 1)
                                                  {
                                                    relocate(&(*(pp)));
                                                  }
                                                  mask >>= 1;
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                          U(tc) = 0;
                          V(tc) = 0;
                          W(tc) = 0;
                          X(tc) = 0;
                          Y(tc) = 0;
                          relocate(&(THREADNO(tc)));
                          relocate(&(CURRENTINPUT(tc)));
                          relocate(&(CURRENTOUTPUT(tc)));
                          relocate(&(CURRENTERROR(tc)));
                          relocate(&(SFD(tc)));
                          relocate(&(CURRENTMSO(tc)));
                          relocate(&(TARGETMACHINE(tc)));
                          relocate(&(FXLENGTHBV(tc)));
                          relocate(&(FXFIRSTBITSETBV(tc)));
                          relocate(&(NULLIMMUTABLEVECTOR(tc)));
                          relocate(&(NULLIMMUTABLEFXVECTOR(tc)));
                          relocate(&(NULLIMMUTABLEBYTEVECTOR(tc)));
                          relocate(&(NULLIMMUTABLESTRING(tc)));
                          relocate(&(COMPILEPROFILE(tc)));
                          relocate(&(SUBSETMODE(tc)));
                          relocate(&(DEFAULTRECORDEQUALPROCEDURE(tc)));
                          relocate(&(DEFAULTRECORDHASHPROCEDURE(tc)));
                          relocate(&(COMPRESSFORMAT(tc)));
                          relocate(&(COMPRESSLEVEL(tc)));
                          relocate(&(PARAMETERS(tc)));
                          DSTBV(tc) = Sfalse;
                          SRCBV(tc) = Sfalse;
                          {
                            INT i = 0;
                            while (i < virtual_register_count)
                            {
                              relocate(&(VIRTREG(tc, i)));
                              i += 1;
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      else if ((iptr)tf == type_rtd_counts)
      {
      }
      else if ((iptr)tf == type_phantom)
      {
      }
      else
      {
        S_error_abort("sweep: illegal typed object type");
      }
    }
    else if (t == type_pair)
    {
      {
        ISPC p_at_spc = SPACE(p);
        if (p_at_spc == space_ephemeron)
        {
          add_ephemeron_to_pending(p);
        }
        else if (p_at_spc == space_weakpair)
        {
          relocate(&INITCDR(p));
        }
        else
        {
          relocate(&INITCAR(p));
          relocate(&INITCDR(p));
        }
      }
    }
    else if (t == type_closure)
    {
      ptr code = CLOSCODE(p);
      relocate(&code);
      if ((CODETYPE(code)) & (code_flag_continuation << code_flags_offset))
      {
        SETCLOSCODE(p, code);
        relocate(&CONTWINDERS(p));
        relocate(&CONTATTACHMENTS(p));
        if ((CONTLENGTH(p)) == scaled_shot_1_shot_flag)
        {
        }
        else
        {
          if (OLDSPACE((CONTSTACK(p))))
          {
            CONTSTACK(p) = copy_stack(CONTSTACK(p), &(CONTLENGTH(p)), CONTCLENGTH(p));
          }
          S_G.countof[target_generation][countof_stack] += 1;
          S_G.bytesof[target_generation][countof_stack] += CONTLENGTH(p);
          relocate(&CONTLINK(p));
          {
            ptr xcp = CONTRET(p);
            {
              iptr co = (ENTRYOFFSET(xcp)) + (((uptr)xcp) - ((uptr)(TO_PTR((ENTRYOFFSETADDR(xcp))))));
              {
                ptr c_p = (ptr)(((uptr)xcp) - co);
                {
                  seginfo* x_si = SegInfo((ptr_get_segment(c_p)));
                  if (x_si -> old_space)
                  {
                    relocate_code(c_p, x_si);
                    CONTRET(p) = (ptr)(((uptr)c_p) + co);
                  }
                  {
                    uptr stack = (uptr)(CONTSTACK(p));
                    {
                      uptr base = stack;
                      {
                        uptr fp = stack + (CONTCLENGTH(p));
                        {
                          uptr ret = (uptr)(CONTRET(p));
                          while (fp != base)
                          {
                            if (fp < base)
                            {
                              S_error_abort("sweep_stack(gc): malformed stack");
                            }
                            fp = fp - (ENTRYFRAMESIZE(ret));
                            {
                              ptr* pp = (ptr*)(TO_VOIDP(fp));
                              iptr oldret = ret;
                              ret = (iptr)(*(pp));
                              {
                                ptr xcp = *(pp);
                                {
                                  iptr co = (ENTRYOFFSET(xcp)) + (((uptr)xcp) - ((uptr)(TO_PTR((ENTRYOFFSETADDR(xcp))))));
                                  {
                                    ptr c_p = (ptr)(((uptr)xcp) - co);
                                    {
                                      seginfo* x_si = SegInfo((ptr_get_segment(c_p)));
                                      if (x_si -> old_space)
                                      {
                                        relocate_code(c_p, x_si);
                                        *(pp) = (ptr)(((uptr)c_p) + co);
                                      }
                                      {
                                        ptr num = ENTRYLIVEMASK(oldret);
                                        if (Sfixnump(num))
                                        {
                                          {
                                            uptr mask = UNFIX(num);
                                            while (mask != 0)
                                            {
                                              pp += 1;
                                              if (mask & 1)
                                              {
                                                relocate(&(*(pp)));
                                              }
                                              mask >>= 1;
                                            }
                                          }
                                        }
                                        else
                                        {
                                          relocate(&(*((ENTRYNONCOMPACTLIVEMASKADDR(oldret)))));
                                          {
                                            ptr num = ENTRYLIVEMASK(oldret);
                                            iptr index = BIGLEN(num);
                                            while (index != 0)
                                            {
                                              index -= 1;
                                              {
                                                INT bits = bigit_bits;
                                                bigit mask = BIGIT(num, index);
                                                while (bits > 0)
                                                {
                                                  bits -= 1;
                                                  pp += 1;
                                                  if (mask & 1)
                                                  {
                                                    relocate(&(*(pp)));
                                                  }
                                                  mask >>= 1;
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      else
      {
        uptr len = CODEFREE(code);
        SETCLOSCODE(p, code);
        {
          uptr idx, p_len = len;
          ptr *p_p = &CLOSIT(p, 0);
          for (idx = 0; idx < p_len; idx++)
          {
            relocate(&(p_p[idx]));
          }
        }
      }
    }
    else if (t == type_symbol)
    {
      ptr val = INITSYMVAL(p);
      relocate(&val);
      INITSYMVAL(p) = val;
      {
        ptr code = ((Sprocedurep(val))
                    ? (CLOSCODE(val))
                    : (SYMCODE(p)));
        relocate(&code);
        INITSYMCODE(p, code);
        relocate(&INITSYMPLIST(p));
        relocate(&INITSYMNAME(p));
        relocate(&INITSYMSPLIST(p));
        relocate(&INITSYMHASH(p));
      }
    }
    else if (t == type_flonum)
    {
    }
    else
    {
      S_error_abort("sweep: illegal type");
    }
  }
  POP_BACKREFERENCE()
}

static IGEN sweep_dirty_object(ptr p, IGEN tg, IGEN youngest)
{
  PUSH_BACKREFERENCE(p)
  {
    ITYPE t = TYPEBITS(p);
    if (t == type_typed_object)
    {
      ptr tf = TYPEFIELD(p);
      if (TYPEP(tf, mask_record, type_record))
      {
        {
          ptr rtd = RECORDINSTTYPE(p);
          {
            ptr num = RECORDDESCMPM(rtd);
            ptr* pp = &(RECORDINSTIT(p, 0));
            if (Sfixnump(num))
            {
              {
                uptr mask = ((uptr)(UNFIX(num))) >> 1;
                while (mask != 0)
                {
                  if (mask & 1)
                  {
                    relocate_dirty(&(*(pp)), tg, youngest);
                  }
                  mask >>= 1;
                  pp += 1;
                }
              }
            }
            else
            {
              {
                iptr index = (BIGLEN(num)) - 1;
                bigit mask = (BIGIT(num, index)) >> 1;
                INT bits = bigit_bits - 1;
                while (1)
                {
                  do
                  {
                    if (mask & 1)
                    {
                      relocate_dirty(&(*(pp)), tg, youngest);
                    }
                    mask >>= 1;
                    pp += 1;
                    bits -= 1;
                  }
                  while (bits > 0);
                  if (index == 0)
                  {
                    break;
                  }
                  index -= 1;
                  mask = BIGIT(num, index);
                  bits = bigit_bits;
                }
              }
            }
          }
        }
      }
      else if (TYPEP(tf, mask_vector, type_vector))
      {
        uptr len = Svector_length(p);
        {
          uptr idx, p_len = len;
          ptr *p_p = &INITVECTIT(p, 0);
          for (idx = 0; idx < p_len; idx++)
          {
            relocate_dirty(&(p_p[idx]), tg, youngest);
          }
        }
      }
      else if (TYPEP(tf, mask_stencil_vector, type_stencil_vector))
      {
        uptr len = Sstencil_vector_length(p);
        {
          uptr idx, p_len = len;
          ptr *p_p = &INITSTENVECTIT(p, 0);
          for (idx = 0; idx < p_len; idx++)
          {
            relocate_dirty(&(p_p[idx]), tg, youngest);
          }
        }
      }
      else if (TYPEP(tf, mask_string, type_string))
      {
      }
      else if (TYPEP(tf, mask_fxvector, type_fxvector))
      {
      }
      else if (TYPEP(tf, mask_bytevector, type_bytevector))
      {
      }
      else if ((iptr)tf == type_tlc)
      {
        relocate_dirty(&INITTLCHT(p), tg, youngest);
        relocate_dirty(&INITTLCKEYVAL(p), tg, youngest);
        relocate_dirty(&INITTLCNEXT(p), tg, youngest);
      }
      else if (TYPEP(tf, mask_box, type_box))
      {
        relocate_dirty(&INITBOXREF(p), tg, youngest);
      }
      else if ((iptr)tf == type_ratnum)
      {
      }
      else if ((iptr)tf == type_exactnum)
      {
      }
      else if ((iptr)tf == type_inexactnum)
      {
      }
      else if (TYPEP(tf, mask_bignum, type_bignum))
      {
      }
      else if (TYPEP(tf, mask_port, type_port))
      {
        relocate_dirty(&PORTHANDLER(p), tg, youngest);
        if (((uptr)tf) & PORT_FLAG_OUTPUT)
        {
          iptr n = ((iptr)(PORTOLAST(p))) - ((iptr)(PORTOBUF(p)));
          relocate_dirty(&PORTOBUF(p), tg, youngest);
          PORTOLAST(p) = (ptr)(((iptr)(PORTOBUF(p))) + n);
        }
        if (((uptr)tf) & PORT_FLAG_INPUT)
        {
          iptr n = ((iptr)(PORTILAST(p))) - ((iptr)(PORTIBUF(p)));
          relocate_dirty(&PORTIBUF(p), tg, youngest);
          PORTILAST(p) = (ptr)(((iptr)(PORTIBUF(p))) + n);
        }
        relocate_dirty(&PORTINFO(p), tg, youngest);
        relocate_dirty(&PORTNAME(p), tg, youngest);
      }
      else if (TYPEP(tf, mask_code, type_code))
      {
      }
      else if ((iptr)tf == type_thread)
      {
      }
      else if ((iptr)tf == type_rtd_counts)
      {
      }
      else if ((iptr)tf == type_phantom)
      {
      }
      else
      {
        S_error_abort("sweep: illegal typed object type");
      }
    }
    else if (t == type_pair)
    {
      {
        ISPC p_at_spc = SPACE(p);
        if (p_at_spc == space_ephemeron)
        {
          add_ephemeron_to_pending(p);
        }
        else if (p_at_spc == space_weakpair)
        {
          relocate_dirty(&INITCDR(p), tg, youngest);
        }
        else
        {
          relocate_dirty(&INITCAR(p), tg, youngest);
          relocate_dirty(&INITCDR(p), tg, youngest);
        }
      }
    }
    else if (t == type_closure)
    {
      ptr code = CLOSCODE(p);
      {
        uptr len = CODEFREE(code);
        if ((CODETYPE(code)) & (code_flag_mutable_closure << code_flags_offset))
        {
          {
            uptr idx, p_len = len;
            ptr *p_p = &CLOSIT(p, 0);
            for (idx = 0; idx < p_len; idx++)
            {
              relocate_dirty(&(p_p[idx]), tg, youngest);
            }
          }
        }
      }
    }
    else if (t == type_symbol)
    {
      ptr val = INITSYMVAL(p);
      relocate_dirty(&val, tg, youngest);
      INITSYMVAL(p) = val;
      {
        ptr code = ((Sprocedurep(val))
                    ? (CLOSCODE(val))
                    : (SYMCODE(p)));
        relocate_dirty(&code, tg, youngest);
        INITSYMCODE(p, code);
        relocate_dirty(&INITSYMPLIST(p), tg, youngest);
        relocate_dirty(&INITSYMNAME(p), tg, youngest);
        relocate_dirty(&INITSYMSPLIST(p), tg, youngest);
        relocate_dirty(&INITSYMHASH(p), tg, youngest);
      }
    }
    else if (t == type_flonum)
    {
    }
    else
    {
      S_error_abort("sweep: illegal type");
    }
  }
  POP_BACKREFERENCE()
  return youngest;
}

static void sweep_record(ptr p)
{
  PUSH_BACKREFERENCE(p)
  {
    {
      ptr rtd = RECORDINSTTYPE(p);
      {
        uptr len = UNFIX((RECORDDESCSIZE(rtd)));
        {
          ptr num = RECORDDESCPM(rtd);
          ptr* pp = &(RECORDINSTIT(p, 0));
          if (Sfixnump(num))
          {
            {
              uptr mask = ((uptr)(UNFIX(num))) >> 1;
              if (mask == (((uptr)-1) >> 1))
              {
                {
                  ptr* ppend = ((ptr*)(TO_VOIDP((((uptr)(TO_PTR(pp))) + len)))) - 1;
                  while (pp < ppend)
                  {
                    relocate(&(*(pp)));
                    pp += 1;
                  }
                }
              }
              else
              {
                while (mask != 0)
                {
                  if (mask & 1)
                  {
                    relocate(&(*(pp)));
                  }
                  mask >>= 1;
                  pp += 1;
                }
              }
            }
          }
          else
          {
            relocate(&(RECORDDESCPM(rtd)));
            num = RECORDDESCPM(rtd);
            {
              iptr index = (BIGLEN(num)) - 1;
              bigit mask = (BIGIT(num, index)) >> 1;
              INT bits = bigit_bits - 1;
              while (1)
              {
                do
                {
                  if (mask & 1)
                  {
                    relocate(&(*(pp)));
                  }
                  mask >>= 1;
                  pp += 1;
                  bits -= 1;
                }
                while (bits > 0);
                if (index == 0)
                {
                  break;
                }
                index -= 1;
                mask = BIGIT(num, index);
                bits = bigit_bits;
              }
            }
          }
        }
      }
    }
  }
  POP_BACKREFERENCE()
}

static IGEN sweep_dirty_record(ptr p, IGEN tg, IGEN youngest)
{
  PUSH_BACKREFERENCE(p)
  {
    {
      ptr rtd = RECORDINSTTYPE(p);
      {
        ptr num = RECORDDESCMPM(rtd);
        ptr* pp = &(RECORDINSTIT(p, 0));
        if (Sfixnump(num))
        {
          {
            uptr mask = ((uptr)(UNFIX(num))) >> 1;
            while (mask != 0)
            {
              if (mask & 1)
              {
                relocate_dirty(&(*(pp)), tg, youngest);
              }
              mask >>= 1;
              pp += 1;
            }
          }
        }
        else
        {
          {
            iptr index = (BIGLEN(num)) - 1;
            bigit mask = (BIGIT(num, index)) >> 1;
            INT bits = bigit_bits - 1;
            while (1)
            {
              do
              {
                if (mask & 1)
                {
                  relocate_dirty(&(*(pp)), tg, youngest);
                }
                mask >>= 1;
                pp += 1;
                bits -= 1;
              }
              while (bits > 0);
              if (index == 0)
              {
                break;
              }
              index -= 1;
              mask = BIGIT(num, index);
              bits = bigit_bits;
            }
          }
        }
      }
    }
  }
  POP_BACKREFERENCE()
  return youngest;
}

static void sweep_symbol(ptr p)
{
  PUSH_BACKREFERENCE(p)
  {
    {
      ptr val = INITSYMVAL(p);
      relocate(&val);
      INITSYMVAL(p) = val;
      {
        ptr code = ((Sprocedurep(val))
                    ? (CLOSCODE(val))
                    : (SYMCODE(p)));
        relocate(&code);
        INITSYMCODE(p, code);
        relocate(&INITSYMPLIST(p));
        relocate(&INITSYMNAME(p));
        relocate(&INITSYMSPLIST(p));
        relocate(&INITSYMHASH(p));
      }
    }
  }
  POP_BACKREFERENCE()
}

static IGEN sweep_dirty_symbol(ptr p, IGEN tg, IGEN youngest)
{
  PUSH_BACKREFERENCE(p)
  {
    {
      ptr val = INITSYMVAL(p);
      relocate_dirty(&val, tg, youngest);
      INITSYMVAL(p) = val;
      {
        ptr code = ((Sprocedurep(val))
                    ? (CLOSCODE(val))
                    : (SYMCODE(p)));
        relocate_dirty(&code, tg, youngest);
        INITSYMCODE(p, code);
        relocate_dirty(&INITSYMPLIST(p), tg, youngest);
        relocate_dirty(&INITSYMNAME(p), tg, youngest);
        relocate_dirty(&INITSYMSPLIST(p), tg, youngest);
        relocate_dirty(&INITSYMHASH(p), tg, youngest);
      }
    }
  }
  POP_BACKREFERENCE()
  return youngest;
}

static void sweep_thread(ptr p)
{
  PUSH_BACKREFERENCE(p)
  {
    {
      ptr tc = (ptr)(THREADTC(p));
      if (tc != ((ptr)0))
      {
        {
          ptr old_stack = SCHEMESTACK(tc);
          if (OLDSPACE(old_stack))
          {
            {
              iptr clength = ((uptr)(SFP(tc))) - ((uptr)old_stack);
              SCHEMESTACK(tc) = copy_stack(old_stack, &(SCHEMESTACKSIZE(tc)), clength + (sizeof(ptr)));
              S_G.countof[target_generation][countof_stack] += 1;
              S_G.bytesof[target_generation][countof_stack] += SCHEMESTACKSIZE(tc);
              SFP(tc) = (ptr)(((uptr)(SCHEMESTACK(tc))) + clength);
              ESP(tc) = (ptr)((((uptr)(SCHEMESTACK(tc))) + (SCHEMESTACKSIZE(tc))) - stack_slop);
            }
          }
        }
        STACKCACHE(tc) = Snil;
        relocate(&(CCHAIN(tc)));
        relocate(&(STACKLINK(tc)));
        relocate(&(WINDERS(tc)));
        relocate(&(ATTACHMENTS(tc)));
        CACHEDFRAME(tc) = Sfalse;
        {
          ptr xcp = FRAME(tc, 0);
          {
            iptr co = (ENTRYOFFSET(xcp)) + (((uptr)xcp) - ((uptr)(TO_PTR((ENTRYOFFSETADDR(xcp))))));
            {
              ptr c_p = (ptr)(((uptr)xcp) - co);
              {
                seginfo* x_si = SegInfo((ptr_get_segment(c_p)));
                if (x_si -> old_space)
                {
                  relocate_code(c_p, x_si);
                  FRAME(tc, 0) = (ptr)(((uptr)c_p) + co);
                }
                {
                  uptr base = (uptr)(SCHEMESTACK(tc));
                  {
                    uptr fp = (uptr)(SFP(tc));
                    {
                      uptr ret = (uptr)(FRAME(tc, 0));
                      while (fp != base)
                      {
                        if (fp < base)
                        {
                          S_error_abort("sweep_stack(gc): malformed stack");
                        }
                        fp = fp - (ENTRYFRAMESIZE(ret));
                        {
                          ptr* pp = (ptr*)(TO_VOIDP(fp));
                          iptr oldret = ret;
                          ret = (iptr)(*(pp));
                          {
                            ptr xcp = *(pp);
                            {
                              iptr co = (ENTRYOFFSET(xcp)) + (((uptr)xcp) - ((uptr)(TO_PTR((ENTRYOFFSETADDR(xcp))))));
                              {
                                ptr c_p = (ptr)(((uptr)xcp) - co);
                                {
                                  seginfo* x_si = SegInfo((ptr_get_segment(c_p)));
                                  if (x_si -> old_space)
                                  {
                                    relocate_code(c_p, x_si);
                                    *(pp) = (ptr)(((uptr)c_p) + co);
                                  }
                                  {
                                    ptr num = ENTRYLIVEMASK(oldret);
                                    if (Sfixnump(num))
                                    {
                                      {
                                        uptr mask = UNFIX(num);
                                        while (mask != 0)
                                        {
                                          pp += 1;
                                          if (mask & 1)
                                          {
                                            relocate(&(*(pp)));
                                          }
                                          mask >>= 1;
                                        }
                                      }
                                    }
                                    else
                                    {
                                      relocate(&(*((ENTRYNONCOMPACTLIVEMASKADDR(oldret)))));
                                      {
                                        ptr num = ENTRYLIVEMASK(oldret);
                                        iptr index = BIGLEN(num);
                                        while (index != 0)
                                        {
                                          index -= 1;
                                          {
                                            INT bits = bigit_bits;
                                            bigit mask = BIGIT(num, index);
                                            while (bits > 0)
                                            {
                                              bits -= 1;
                                              pp += 1;
                                              if (mask & 1)
                                              {
                                                relocate(&(*(pp)));
                                              }
                                              mask >>= 1;
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                      U(tc) = 0;
                      V(tc) = 0;
                      W(tc) = 0;
                      X(tc) = 0;
                      Y(tc) = 0;
                      relocate(&(THREADNO(tc)));
                      relocate(&(CURRENTINPUT(tc)));
                      relocate(&(CURRENTOUTPUT(tc)));
                      relocate(&(CURRENTERROR(tc)));
                      relocate(&(SFD(tc)));
                      relocate(&(CURRENTMSO(tc)));
                      relocate(&(TARGETMACHINE(tc)));
                      relocate(&(FXLENGTHBV(tc)));
                      relocate(&(FXFIRSTBITSETBV(tc)));
                      relocate(&(NULLIMMUTABLEVECTOR(tc)));
                      relocate(&(NULLIMMUTABLEFXVECTOR(tc)));
                      relocate(&(NULLIMMUTABLEBYTEVECTOR(tc)));
                      relocate(&(NULLIMMUTABLESTRING(tc)));
                      relocate(&(COMPILEPROFILE(tc)));
                      relocate(&(SUBSETMODE(tc)));
                      relocate(&(DEFAULTRECORDEQUALPROCEDURE(tc)));
                      relocate(&(DEFAULTRECORDHASHPROCEDURE(tc)));
                      relocate(&(COMPRESSFORMAT(tc)));
                      relocate(&(COMPRESSLEVEL(tc)));
                      relocate(&(PARAMETERS(tc)));
                      DSTBV(tc) = Sfalse;
                      SRCBV(tc) = Sfalse;
                      {
                        INT i = 0;
                        while (i < virtual_register_count)
                        {
                          relocate(&(VIRTREG(tc, i)));
                          i += 1;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  POP_BACKREFERENCE()
}

static void sweep_port(ptr p)
{
  PUSH_BACKREFERENCE(p)
  {
    relocate(&PORTHANDLER(p));
    if (((uptr)TYPEFIELD(p)) & PORT_FLAG_OUTPUT)
    {
      iptr n = ((iptr)(PORTOLAST(p))) - ((iptr)(PORTOBUF(p)));
      relocate(&PORTOBUF(p));
      PORTOLAST(p) = (ptr)(((iptr)(PORTOBUF(p))) + n);
    }
    if (((uptr)TYPEFIELD(p)) & PORT_FLAG_INPUT)
    {
      iptr n = ((iptr)(PORTILAST(p))) - ((iptr)(PORTIBUF(p)));
      relocate(&PORTIBUF(p));
      PORTILAST(p) = (ptr)(((iptr)(PORTIBUF(p))) + n);
    }
    relocate(&PORTINFO(p));
    relocate(&PORTNAME(p));
  }
  POP_BACKREFERENCE()
}

static IGEN sweep_dirty_port(ptr p, IGEN tg, IGEN youngest)
{
  PUSH_BACKREFERENCE(p)
  {
    relocate_dirty(&PORTHANDLER(p), tg, youngest);
    if (((uptr)TYPEFIELD(p)) & PORT_FLAG_OUTPUT)
    {
      iptr n = ((iptr)(PORTOLAST(p))) - ((iptr)(PORTOBUF(p)));
      relocate_dirty(&PORTOBUF(p), tg, youngest);
      PORTOLAST(p) = (ptr)(((iptr)(PORTOBUF(p))) + n);
    }
    if (((uptr)TYPEFIELD(p)) & PORT_FLAG_INPUT)
    {
      iptr n = ((iptr)(PORTILAST(p))) - ((iptr)(PORTIBUF(p)));
      relocate_dirty(&PORTIBUF(p), tg, youngest);
      PORTILAST(p) = (ptr)(((iptr)(PORTIBUF(p))) + n);
    }
    relocate_dirty(&PORTINFO(p), tg, youngest);
    relocate_dirty(&PORTNAME(p), tg, youngest);
  }
  POP_BACKREFERENCE()
  return youngest;
}

static void sweep_continuation(ptr p)
{
  PUSH_BACKREFERENCE(p)
  {
    {
      relocate(&CONTWINDERS(p));
      relocate(&CONTATTACHMENTS(p));
      if ((CONTLENGTH(p)) == scaled_shot_1_shot_flag)
      {
      }
      else
      {
        if (OLDSPACE((CONTSTACK(p))))
        {
          CONTSTACK(p) = copy_stack(CONTSTACK(p), &(CONTLENGTH(p)), CONTCLENGTH(p));
        }
        S_G.countof[target_generation][countof_stack] += 1;
        S_G.bytesof[target_generation][countof_stack] += CONTLENGTH(p);
        relocate(&CONTLINK(p));
        {
          ptr xcp = CONTRET(p);
          {
            iptr co = (ENTRYOFFSET(xcp)) + (((uptr)xcp) - ((uptr)(TO_PTR((ENTRYOFFSETADDR(xcp))))));
            {
              ptr c_p = (ptr)(((uptr)xcp) - co);
              {
                seginfo* x_si = SegInfo((ptr_get_segment(c_p)));
                if (x_si -> old_space)
                {
                  relocate_code(c_p, x_si);
                  CONTRET(p) = (ptr)(((uptr)c_p) + co);
                }
                {
                  uptr stack = (uptr)(CONTSTACK(p));
                  {
                    uptr base = stack;
                    {
                      uptr fp = stack + (CONTCLENGTH(p));
                      {
                        uptr ret = (uptr)(CONTRET(p));
                        while (fp != base)
                        {
                          if (fp < base)
                          {
                            S_error_abort("sweep_stack(gc): malformed stack");
                          }
                          fp = fp - (ENTRYFRAMESIZE(ret));
                          {
                            ptr* pp = (ptr*)(TO_VOIDP(fp));
                            iptr oldret = ret;
                            ret = (iptr)(*(pp));
                            {
                              ptr xcp = *(pp);
                              {
                                iptr co = (ENTRYOFFSET(xcp)) + (((uptr)xcp) - ((uptr)(TO_PTR((ENTRYOFFSETADDR(xcp))))));
                                {
                                  ptr c_p = (ptr)(((uptr)xcp) - co);
                                  {
                                    seginfo* x_si = SegInfo((ptr_get_segment(c_p)));
                                    if (x_si -> old_space)
                                    {
                                      relocate_code(c_p, x_si);
                                      *(pp) = (ptr)(((uptr)c_p) + co);
                                    }
                                    {
                                      ptr num = ENTRYLIVEMASK(oldret);
                                      if (Sfixnump(num))
                                      {
                                        {
                                          uptr mask = UNFIX(num);
                                          while (mask != 0)
                                          {
                                            pp += 1;
                                            if (mask & 1)
                                            {
                                              relocate(&(*(pp)));
                                            }
                                            mask >>= 1;
                                          }
                                        }
                                      }
                                      else
                                      {
                                        relocate(&(*((ENTRYNONCOMPACTLIVEMASKADDR(oldret)))));
                                        {
                                          ptr num = ENTRYLIVEMASK(oldret);
                                          iptr index = BIGLEN(num);
                                          while (index != 0)
                                          {
                                            index -= 1;
                                            {
                                              INT bits = bigit_bits;
                                              bigit mask = BIGIT(num, index);
                                              while (bits > 0)
                                              {
                                                bits -= 1;
                                                pp += 1;
                                                if (mask & 1)
                                                {
                                                  relocate(&(*(pp)));
                                                }
                                                mask >>= 1;
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  POP_BACKREFERENCE()
}

static void sweep_code_object(ptr tc_in, ptr p)
{
  PUSH_BACKREFERENCE(p)
  {
    relocate(&CODENAME(p));
    relocate(&CODEARITYMASK(p));
    relocate(&CODEINFO(p));
    relocate(&CODEPINFOS(p));
    {
      ptr t = CODERELOC(p);
      {
        iptr m = RELOCSIZE(t);
        {
          ptr oldco = RELOCCODE(t);
          {
            iptr a = 0;
            {
              iptr n = 0;
              while (n < m)
              {
                {
                  uptr entry = RELOCIT(t, n);
                  uptr item_off = 0;
                  uptr code_off = 0;
                  n = n + 1;
                  if (RELOC_EXTENDED_FORMAT(entry))
                  {
                    item_off = RELOCIT(t, n);
                    n = n + 1;
                    code_off = RELOCIT(t, n);
                    n = n + 1;
                  }
                  else
                  {
                    item_off = RELOC_ITEM_OFFSET(entry);
                    code_off = RELOC_CODE_OFFSET(entry);
                  }
                  a = a + code_off;
                  {
                    ptr obj = S_get_code_obj(RELOC_TYPE(entry), oldco, a, item_off);
                    relocate(&obj);
                    S_set_code_obj("gc", RELOC_TYPE(entry), p, a, obj, item_off);
                  }
                }
              }
              if ((target_generation == static_generation) && ((!S_G.retain_static_relocation) && (0 == ((CODETYPE(p)) & (code_flag_template << code_flags_offset)))))
              {
                CODERELOC(p) = (ptr)0;
              }
              else
              {
                {
                  seginfo* t_si = SegInfo((ptr_get_segment(t)));
                  if (t_si -> old_space)
                  {
                    n = size_reloc_table((RELOCSIZE(t)));
                    S_G.countof[target_generation][countof_relocation_table] += 1;
                    S_G.bytesof[target_generation][countof_relocation_table] += n;
                    if (t_si -> use_marks)
                    {
                      mark_typemod_data_object(t, n, t_si);
                    }
                    else
                    {
                      {
                        ptr oldt = t;
                        find_room(space_data, target_generation, typemod, n, t);
                        memcpy_aligned(TO_VOIDP(t), TO_VOIDP(oldt), n);
                      }
                    }
                  }
                }
                RELOCCODE(t) = p;
                CODERELOC(p) = t;
              }
              S_record_code_mod(tc_in, (uptr)(TO_PTR((&(CODEIT(p, 0))))), (uptr)(CODELEN(p)));
            }
          }
        }
      }
    }
  }
  POP_BACKREFERENCE()
}

static uptr size_object(ptr p)
{
  ITYPE t = TYPEBITS(p);
  if (t == type_typed_object)
  {
    ptr tf = TYPEFIELD(p);
    if (TYPEP(tf, mask_record, type_record))
    {
      {
        ptr rtd = RECORDINSTTYPE(p);
        {
          uptr len = UNFIX((RECORDDESCSIZE(rtd)));
          {
            uptr p_sz = size_record_inst(len);
            return p_sz;
          }
        }
      }
    }
    else if (TYPEP(tf, mask_vector, type_vector))
    {
      uptr len = Svector_length(p);
      {
        uptr p_sz = size_vector(len);
        return p_sz;
      }
    }
    else if (TYPEP(tf, mask_stencil_vector, type_stencil_vector))
    {
      uptr len = Sstencil_vector_length(p);
      {
        uptr p_sz = size_stencil_vector(len);
        return p_sz;
      }
    }
    else if (TYPEP(tf, mask_string, type_string))
    {
      uptr sz = size_string((Sstring_length(p)));
      {
        uptr p_sz = sz;
        return p_sz;
      }
    }
    else if (TYPEP(tf, mask_fxvector, type_fxvector))
    {
      uptr sz = size_fxvector((Sfxvector_length(p)));
      {
        uptr p_sz = sz;
        return p_sz;
      }
    }
    else if (TYPEP(tf, mask_bytevector, type_bytevector))
    {
      uptr sz = size_bytevector((Sbytevector_length(p)));
      {
        uptr p_sz = sz;
        return p_sz;
      }
    }
    else if ((iptr)tf == type_tlc)
    {
      uptr p_sz = size_tlc;
      return p_sz;
    }
    else if (TYPEP(tf, mask_box, type_box))
    {
      uptr p_sz = size_box;
      return p_sz;
    }
    else if ((iptr)tf == type_ratnum)
    {
      uptr p_sz = size_ratnum;
      return p_sz;
    }
    else if ((iptr)tf == type_exactnum)
    {
      uptr p_sz = size_exactnum;
      return p_sz;
    }
    else if ((iptr)tf == type_inexactnum)
    {
      uptr p_sz = size_inexactnum;
      return p_sz;
    }
    else if (TYPEP(tf, mask_bignum, type_bignum))
    {
      uptr sz = size_bignum((BIGLEN(p)));
      {
        uptr p_sz = sz;
        return p_sz;
      }
    }
    else if (TYPEP(tf, mask_port, type_port))
    {
      uptr p_sz = size_port;
      return p_sz;
    }
    else if (TYPEP(tf, mask_code, type_code))
    {
      uptr len = CODELEN(p);
      {
        uptr p_sz = size_code(len);
        return p_sz;
      }
    }
    else if ((iptr)tf == type_thread)
    {
      uptr p_sz = size_thread;
      return p_sz;
    }
    else if ((iptr)tf == type_rtd_counts)
    {
      uptr p_sz = size_rtd_counts;
      return p_sz;
    }
    else if ((iptr)tf == type_phantom)
    {
      uptr p_sz = size_phantom;
      return p_sz;
    }
    else
    {
      S_error_abort("size: illegal typed object type");
    }
  }
  else if (t == type_pair)
  {
    {
      ISPC p_at_spc = SPACE(p);
      if (p_at_spc == space_ephemeron)
      {
        uptr p_sz = size_ephemeron;
        return p_sz;
      }
      else if (p_at_spc == space_weakpair)
      {
        uptr p_sz = size_pair;
        return p_sz;
      }
      else
      {
        uptr p_sz = size_pair;
        return p_sz;
      }
    }
  }
  else if (t == type_closure)
  {
    ptr code = CLOSCODE(p);
    if ((CODETYPE(code)) & (code_flag_continuation << code_flags_offset))
    {
      uptr p_sz = size_continuation;
      return p_sz;
    }
    else
    {
      uptr len = CODEFREE(code);
      {
        uptr p_sz = size_closure(len);
        return p_sz;
      }
    }
  }
  else if (t == type_symbol)
  {
    uptr p_sz = size_symbol;
    return p_sz;
  }
  else if (t == type_flonum)
  {
    uptr p_sz = size_flonum;
    return p_sz;
  }
  else
  {
    S_error_abort("size: illegal type");
  }
}

static void mark_object(ptr p, seginfo *si)
{
  change = 1;
  check_triggers(si);
  if (!si->marked_mask) {
    find_room_voidp(space_data, target_generation, ptr_align(segment_bitmap_bytes), si->marked_mask);
    memset(si->marked_mask, 0, segment_bitmap_bytes);
  }
  {
    ITYPE t = TYPEBITS(p);
    if (t == type_typed_object)
    {
      ptr tf = TYPEFIELD(p);
      if (TYPEP(tf, mask_record, type_record))
      {
        /* Relocate to make sure we aren't using an oldspace descriptor
           that has been overwritten by a forwarding marker, but don't loop
           on tag-reflexive base descriptor */
        if (p != tf)
        {
          relocate(&RECORDINSTTYPE(p));
        }
        {
          ptr rtd = RECORDINSTTYPE(p);
          {
            uptr len = UNFIX((RECORDDESCSIZE(rtd)));
            {
              uptr p_sz = size_record_inst(len);
              {
                uptr addr = (uptr)UNTYPE(p, type_typed_object);
                if (addr_get_segment(addr) == addr_get_segment(addr + p_sz - 1))
                {
                  si->marked_count += p_sz;
                  {
                    uptr offset = 0;
                    while (offset < p_sz) {
                      ptr mark_p = (ptr)((uptr)p + offset);
                      si->marked_mask[segment_bitmap_byte(mark_p)] |= segment_bitmap_bit(mark_p);
                      offset += byte_alignment;
                    }
                  }
                }
                else
                {
                  uptr offset = 0;
                  while (offset < p_sz) {
                    ptr mark_p = (ptr)((uptr)p + offset);
                    seginfo *mark_si = SegInfo(ptr_get_segment(mark_p));
                    if (!mark_si->marked_mask) {
                      find_room_voidp(space_data, target_generation, ptr_align(segment_bitmap_bytes), mark_si->marked_mask);
                      memset(mark_si->marked_mask, 0, segment_bitmap_bytes);
                    }
                    mark_si->marked_mask[segment_bitmap_byte(mark_p)] |= segment_bitmap_bit(mark_p);
                    mark_si->marked_count += byte_alignment;
                    offset += byte_alignment;
                  }
                }
              }
              if (!is_counting_root(si, p))
              {
                push_sweep(p);
              }
              if (S_G.enable_object_counts)
              {
                {
                  ptr c_rtd = ((tf == p)
                               ? p
                               : rtd);
                  ptr counts = RECORDDESCCOUNTS(c_rtd);
                  if (counts == Sfalse)
                  {
                    {
                      IGEN grtd = GENERATION(c_rtd);
                      (S_G.countof[grtd])[countof_rtd_counts] += 1;
                      find_room(space_data, grtd, type_typed_object, size_rtd_counts, counts);
                      RTDCOUNTSTYPE(counts) = type_rtd_counts;
                      RTDCOUNTSTIMESTAMP(counts) = S_G.gctimestamp[0];
                      {
                        IGEN g = 0;
                        while (g <= static_generation)
                        {
                          RTDCOUNTSIT(counts, g) = 0;
                          g += 1;
                        }
                      }
                      RECORDDESCCOUNTS(c_rtd) = counts;
                      S_G.rtds_with_counts[grtd] = S_cons_in(((grtd <= max_copied_generation) ? space_new : space_impure), ((grtd <= max_copied_generation) ? 0 : grtd), c_rtd, S_G.rtds_with_counts[grtd]);
                      (S_G.countof[grtd])[countof_pair] += 1;
                    }
                  }
                  else
                  {
                    relocate(&counts);
                    RECORDDESCCOUNTS(c_rtd) = counts;
                    if ((RTDCOUNTSTIMESTAMP(counts)) != (S_G.gctimestamp[0]))
                    {
                      S_fixup_counts(counts);
                    }
                  }
                  RTDCOUNTSIT(counts, target_generation) = (RTDCOUNTSIT(counts, target_generation)) + 1;
                }
              }
              S_G.countof[target_generation][countof_record] += 1;
              S_G.bytesof[target_generation][countof_record] += p_sz;
            }
          }
        }
      }
      else if (TYPEP(tf, mask_vector, type_vector))
      {
        uptr len = Svector_length(p);
        {
          uptr p_sz = size_vector(len);
          {
            uptr addr = (uptr)UNTYPE(p, type_typed_object);
            if (addr_get_segment(addr) == addr_get_segment(addr + p_sz - 1))
            {
              si->marked_count += p_sz;
              {
                uptr offset = 0;
                while (offset < p_sz) {
                  ptr mark_p = (ptr)((uptr)p + offset);
                  si->marked_mask[segment_bitmap_byte(mark_p)] |= segment_bitmap_bit(mark_p);
                  offset += byte_alignment;
                }
              }
            }
            else
            {
              uptr offset = 0;
              while (offset < p_sz) {
                ptr mark_p = (ptr)((uptr)p + offset);
                seginfo *mark_si = SegInfo(ptr_get_segment(mark_p));
                if (!mark_si->marked_mask) {
                  find_room_voidp(space_data, target_generation, ptr_align(segment_bitmap_bytes), mark_si->marked_mask);
                  memset(mark_si->marked_mask, 0, segment_bitmap_bytes);
                }
                mark_si->marked_mask[segment_bitmap_byte(mark_p)] |= segment_bitmap_bit(mark_p);
                mark_si->marked_count += byte_alignment;
                offset += byte_alignment;
              }
            }
          }
          push_sweep(p);
          S_G.countof[target_generation][countof_vector] += 1;
          S_G.bytesof[target_generation][countof_vector] += p_sz;
        }
      }
      else if (TYPEP(tf, mask_stencil_vector, type_stencil_vector))
      {
        uptr len = Sstencil_vector_length(p);
        {
          uptr p_sz = size_stencil_vector(len);
          si->marked_count += p_sz;
          {
            uptr offset = 0;
            while (offset < p_sz) {
              ptr mark_p = (ptr)((uptr)p + offset);
              si->marked_mask[segment_bitmap_byte(mark_p)] |= segment_bitmap_bit(mark_p);
              offset += byte_alignment;
            }
          }
          push_sweep(p);
          S_G.countof[target_generation][countof_stencil_vector] += 1;
          S_G.bytesof[target_generation][countof_stencil_vector] += p_sz;
        }
      }
      else if (TYPEP(tf, mask_string, type_string))
      {
        uptr sz = size_string((Sstring_length(p)));
        {
          uptr p_sz = sz;
          si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
          {
            uptr addr = (uptr)UNTYPE(p, type_typed_object);
            uptr seg = addr_get_segment(addr);
            uptr end_seg = addr_get_segment(addr + p_sz - 1);
            if (seg == end_seg) {
              si->marked_count += p_sz;
            } else {
              seginfo *mark_si;
              si->marked_count += ((uptr)build_ptr(seg+1,0)) - addr;
              seg++;
              while (seg < end_seg) {
                mark_si = SegInfo(seg);
                if (!fully_marked_mask) init_fully_marked_mask();
                mark_si->marked_mask = fully_marked_mask;
                mark_si->marked_count = segment_bitmap_bytes;
                seg++;
              }
              mark_si = SegInfo(end_seg);
              if (!mark_si->marked_mask) {
                find_room_voidp(space_data, target_generation, ptr_align(segment_bitmap_bytes), mark_si->marked_mask);
                memset(mark_si->marked_mask, 0, segment_bitmap_bytes);
              }
                /* no need to set a bit: just make sure `marked_mask` is non-NULL */
              mark_si->marked_count += addr + p_sz - (uptr)build_ptr(end_seg,0);
            }
          }
          S_G.countof[target_generation][countof_string] += 1;
          S_G.bytesof[target_generation][countof_string] += p_sz;
        }
      }
      else if (TYPEP(tf, mask_fxvector, type_fxvector))
      {
        uptr sz = size_fxvector((Sfxvector_length(p)));
        {
          uptr p_sz = sz;
          si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
          {
            uptr addr = (uptr)UNTYPE(p, type_typed_object);
            uptr seg = addr_get_segment(addr);
            uptr end_seg = addr_get_segment(addr + p_sz - 1);
            if (seg == end_seg) {
              si->marked_count += p_sz;
            } else {
              seginfo *mark_si;
              si->marked_count += ((uptr)build_ptr(seg+1,0)) - addr;
              seg++;
              while (seg < end_seg) {
                mark_si = SegInfo(seg);
                if (!fully_marked_mask) init_fully_marked_mask();
                mark_si->marked_mask = fully_marked_mask;
                mark_si->marked_count = segment_bitmap_bytes;
                seg++;
              }
              mark_si = SegInfo(end_seg);
              if (!mark_si->marked_mask) {
                find_room_voidp(space_data, target_generation, ptr_align(segment_bitmap_bytes), mark_si->marked_mask);
                memset(mark_si->marked_mask, 0, segment_bitmap_bytes);
              }
                /* no need to set a bit: just make sure `marked_mask` is non-NULL */
              mark_si->marked_count += addr + p_sz - (uptr)build_ptr(end_seg,0);
            }
          }
          S_G.countof[target_generation][countof_fxvector] += 1;
          S_G.bytesof[target_generation][countof_fxvector] += p_sz;
        }
      }
      else if (TYPEP(tf, mask_bytevector, type_bytevector))
      {
        uptr sz = size_bytevector((Sbytevector_length(p)));
        {
          uptr p_sz = sz;
          si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
          {
            uptr addr = (uptr)UNTYPE(p, type_typed_object);
            uptr seg = addr_get_segment(addr);
            uptr end_seg = addr_get_segment(addr + p_sz - 1);
            if (seg == end_seg) {
              si->marked_count += p_sz;
            } else {
              seginfo *mark_si;
              si->marked_count += ((uptr)build_ptr(seg+1,0)) - addr;
              seg++;
              while (seg < end_seg) {
                mark_si = SegInfo(seg);
                if (!fully_marked_mask) init_fully_marked_mask();
                mark_si->marked_mask = fully_marked_mask;
                mark_si->marked_count = segment_bitmap_bytes;
                seg++;
              }
              mark_si = SegInfo(end_seg);
              if (!mark_si->marked_mask) {
                find_room_voidp(space_data, target_generation, ptr_align(segment_bitmap_bytes), mark_si->marked_mask);
                memset(mark_si->marked_mask, 0, segment_bitmap_bytes);
              }
                /* no need to set a bit: just make sure `marked_mask` is non-NULL */
              mark_si->marked_count += addr + p_sz - (uptr)build_ptr(end_seg,0);
            }
          }
          S_G.countof[target_generation][countof_bytevector] += 1;
          S_G.bytesof[target_generation][countof_bytevector] += p_sz;
        }
      }
      else if ((iptr)tf == type_tlc)
      {
        uptr p_sz = size_tlc;
        si->marked_count += p_sz;
        {
          ptr mark_p = p;
          si->marked_mask[segment_bitmap_byte(mark_p)] |= segment_bitmap_bit(mark_p);
          mark_p = (ptr)((uptr)mark_p + byte_alignment);
          si->marked_mask[segment_bitmap_byte(mark_p)] |= segment_bitmap_bit(mark_p);
        }
        push_sweep(p);
        {
          ptr next = INITTLCNEXT(p);
          {
            ptr keyval = INITTLCKEYVAL(p);
            if ((next != Sfalse) && (OLDSPACE(keyval)))
            {
              tlcs_to_rehash = S_cons_in(space_new, 0, p, tlcs_to_rehash);
            }
            S_G.countof[target_generation][countof_tlc] += 1;
          }
        }
      }
      else if (TYPEP(tf, mask_box, type_box))
      {
        uptr p_sz = size_box;
        si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
        si->marked_count += p_sz;
        push_sweep(p);
        S_G.countof[target_generation][countof_box] += 1;
      }
      else if ((iptr)tf == type_ratnum)
      {
        uptr p_sz = size_ratnum;
        relocate(&RATNUM(p));
        relocate(&RATDEN(p));
        si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
        si->marked_count += p_sz;
        S_G.countof[target_generation][countof_ratnum] += 1;
      }
      else if ((iptr)tf == type_exactnum)
      {
        uptr p_sz = size_exactnum;
        relocate(&EXACTNUM_REAL_PART(p));
        relocate(&EXACTNUM_IMAG_PART(p));
        si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
        si->marked_count += p_sz;
        S_G.countof[target_generation][countof_exactnum] += 1;
      }
      else if ((iptr)tf == type_inexactnum)
      {
        uptr p_sz = size_inexactnum;
        si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
        si->marked_count += p_sz;
        S_G.countof[target_generation][countof_inexactnum] += 1;
      }
      else if (TYPEP(tf, mask_bignum, type_bignum))
      {
        uptr sz = size_bignum((BIGLEN(p)));
        {
          uptr p_sz = sz;
          si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
          {
            uptr addr = (uptr)UNTYPE(p, type_typed_object);
            uptr seg = addr_get_segment(addr);
            uptr end_seg = addr_get_segment(addr + p_sz - 1);
            if (seg == end_seg) {
              si->marked_count += p_sz;
            } else {
              seginfo *mark_si;
              si->marked_count += ((uptr)build_ptr(seg+1,0)) - addr;
              seg++;
              while (seg < end_seg) {
                mark_si = SegInfo(seg);
                if (!fully_marked_mask) init_fully_marked_mask();
                mark_si->marked_mask = fully_marked_mask;
                mark_si->marked_count = segment_bitmap_bytes;
                seg++;
              }
              mark_si = SegInfo(end_seg);
              if (!mark_si->marked_mask) {
                find_room_voidp(space_data, target_generation, ptr_align(segment_bitmap_bytes), mark_si->marked_mask);
                memset(mark_si->marked_mask, 0, segment_bitmap_bytes);
              }
                /* no need to set a bit: just make sure `marked_mask` is non-NULL */
              mark_si->marked_count += addr + p_sz - (uptr)build_ptr(end_seg,0);
            }
          }
          S_G.countof[target_generation][countof_bignum] += 1;
          S_G.bytesof[target_generation][countof_bignum] += p_sz;
        }
      }
      else if (TYPEP(tf, mask_port, type_port))
      {
        uptr p_sz = size_port;
        si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
        si->marked_count += p_sz;
        push_sweep(p);
        S_G.countof[target_generation][countof_port] += 1;
      }
      else if (TYPEP(tf, mask_code, type_code))
      {
        uptr len = CODELEN(p);
        {
          uptr p_sz = size_code(len);
          si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
          {
            uptr addr = (uptr)UNTYPE(p, type_typed_object);
            uptr seg = addr_get_segment(addr);
            uptr end_seg = addr_get_segment(addr + p_sz - 1);
            if (seg == end_seg) {
              si->marked_count += p_sz;
            } else {
              seginfo *mark_si;
              si->marked_count += ((uptr)build_ptr(seg+1,0)) - addr;
              seg++;
              while (seg < end_seg) {
                mark_si = SegInfo(seg);
                if (!fully_marked_mask) init_fully_marked_mask();
                mark_si->marked_mask = fully_marked_mask;
                mark_si->marked_count = segment_bitmap_bytes;
                seg++;
              }
              mark_si = SegInfo(end_seg);
              if (!mark_si->marked_mask) {
                find_room_voidp(space_data, target_generation, ptr_align(segment_bitmap_bytes), mark_si->marked_mask);
                memset(mark_si->marked_mask, 0, segment_bitmap_bytes);
              }
                /* no need to set a bit: just make sure `marked_mask` is non-NULL */
              mark_si->marked_count += addr + p_sz - (uptr)build_ptr(end_seg,0);
            }
          }
          push_sweep(p);
          S_G.countof[target_generation][countof_code] += 1;
          S_G.bytesof[target_generation][countof_code] += p_sz;
        }
      }
      else if ((iptr)tf == type_thread)
      {
        uptr p_sz = size_thread;
        si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
        si->marked_count += p_sz;
        push_sweep(p);
        S_G.countof[target_generation][countof_thread] += 1;
      }
      else if ((iptr)tf == type_rtd_counts)
      {
        uptr p_sz = size_rtd_counts;
        si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
        si->marked_count += p_sz;
        S_G.countof[target_generation][countof_rtd_counts] += 1;
      }
      else if ((iptr)tf == type_phantom)
      {
        uptr p_sz = size_phantom;
        si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
        si->marked_count += p_sz;
        S_G.countof[target_generation][countof_phantom] += 1;
        (S_G.bytesof[target_generation])[countof_phantom] += PHANTOMLEN(p);
      }
      else
      {
        S_error_abort("mark: illegal typed object type");
      }
    }
    else if (t == type_pair)
    {
      {
        ISPC p_at_spc = si->space;
        if (p_at_spc == space_ephemeron)
        {
          uptr p_sz = size_ephemeron;
          add_ephemeron_to_pending(p);
          si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
          si->marked_count += p_sz;
          S_G.countof[target_generation][countof_ephemeron] += 1;
        }
        else if (p_at_spc == space_weakpair)
        {
          uptr p_sz = size_pair;
          si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
          si->marked_count += p_sz;
          push_sweep(p);
          S_G.countof[target_generation][countof_weakpair] += 1;
        }
        else
        {
          uptr p_sz = size_pair;
          si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
          si->marked_count += p_sz;
          push_sweep(p);
          S_G.countof[target_generation][countof_pair] += 1;
        }
      }
    }
    else if (t == type_closure)
    {
      ptr code = CLOSCODE(p);
      relocate(&code);
      if ((CODETYPE(code)) & (code_flag_continuation << code_flags_offset))
      {
        uptr p_sz = size_continuation;
        si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
        si->marked_count += p_sz;
        if (!is_counting_root(si, p))
        {
          push_sweep(p);
        }
        S_G.countof[target_generation][countof_continuation] += 1;
      }
      else
      {
        uptr len = CODEFREE(code);
        {
          uptr p_sz = size_closure(len);
          {
            ISPC p_at_spc = si->space;
            if (p_at_spc == space_pure)
            {
              si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
              {
                uptr addr = (uptr)UNTYPE(p, type_closure);
                uptr seg = addr_get_segment(addr);
                uptr end_seg = addr_get_segment(addr + p_sz - 1);
                if (seg == end_seg) {
                  si->marked_count += p_sz;
                } else {
                  seginfo *mark_si;
                  si->marked_count += ((uptr)build_ptr(seg+1,0)) - addr;
                  seg++;
                  while (seg < end_seg) {
                    mark_si = SegInfo(seg);
                    if (!fully_marked_mask) init_fully_marked_mask();
                    mark_si->marked_mask = fully_marked_mask;
                    mark_si->marked_count = segment_bitmap_bytes;
                    seg++;
                  }
                  mark_si = SegInfo(end_seg);
                  if (!mark_si->marked_mask) {
                    find_room_voidp(space_data, target_generation, ptr_align(segment_bitmap_bytes), mark_si->marked_mask);
                    memset(mark_si->marked_mask, 0, segment_bitmap_bytes);
                  }
                    /* no need to set a bit: just make sure `marked_mask` is non-NULL */
                  mark_si->marked_count += addr + p_sz - (uptr)build_ptr(end_seg,0);
                }
              }
              if (!is_counting_root(si, p))
              {
                push_sweep(p);
              }
              S_G.countof[target_generation][countof_closure] += 1;
              S_G.bytesof[target_generation][countof_closure] += p_sz;
            }
            else
            {
              {
                uptr addr = (uptr)UNTYPE(p, type_closure);
                if (addr_get_segment(addr) == addr_get_segment(addr + p_sz - 1))
                {
                  si->marked_count += p_sz;
                  {
                    uptr offset = 0;
                    while (offset < p_sz) {
                      ptr mark_p = (ptr)((uptr)p + offset);
                      si->marked_mask[segment_bitmap_byte(mark_p)] |= segment_bitmap_bit(mark_p);
                      offset += byte_alignment;
                    }
                  }
                }
                else
                {
                  uptr offset = 0;
                  while (offset < p_sz) {
                    ptr mark_p = (ptr)((uptr)p + offset);
                    seginfo *mark_si = SegInfo(ptr_get_segment(mark_p));
                    if (!mark_si->marked_mask) {
                      find_room_voidp(space_data, target_generation, ptr_align(segment_bitmap_bytes), mark_si->marked_mask);
                      memset(mark_si->marked_mask, 0, segment_bitmap_bytes);
                    }
                    mark_si->marked_mask[segment_bitmap_byte(mark_p)] |= segment_bitmap_bit(mark_p);
                    mark_si->marked_count += byte_alignment;
                    offset += byte_alignment;
                  }
                }
              }
              if (!is_counting_root(si, p))
              {
                push_sweep(p);
              }
              S_G.countof[target_generation][countof_closure] += 1;
              S_G.bytesof[target_generation][countof_closure] += p_sz;
            }
          }
          S_G.countof[target_generation][countof_closure] += 1;
          S_G.bytesof[target_generation][countof_closure] += p_sz;
        }
      }
    }
    else if (t == type_symbol)
    {
      uptr p_sz = size_symbol;
      si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
      si->marked_count += p_sz;
      push_sweep(p);
      S_G.countof[target_generation][countof_symbol] += 1;
    }
    else if (t == type_flonum)
    {
      uptr p_sz = size_flonum;
      si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
      si->marked_count += p_sz;
      S_G.countof[target_generation][countof_flonum] += 1;
    }
    else
    {
      S_error_abort("mark: illegal type");
    }
  }
  ADD_BACKREFERENCE(p)
}

static IBOOL object_directly_refers_to_self(ptr p)
{
  {
    ITYPE t = TYPEBITS(p);
    if (t == type_typed_object)
    {
      ptr tf = TYPEFIELD(p);
      if (TYPEP(tf, mask_record, type_record))
      {
        {
          ptr rtd = RECORDINSTTYPE(p);
          {
            uptr len = UNFIX((RECORDDESCSIZE(rtd)));
            {
              ptr num = RECORDDESCPM(rtd);
              ptr* pp = &(RECORDINSTIT(p, 0));
              if (Sfixnump(num))
              {
                {
                  uptr mask = ((uptr)(UNFIX(num))) >> 1;
                  if (mask == (((uptr)-1) >> 1))
                  {
                    {
                      ptr* ppend = ((ptr*)(TO_VOIDP((((uptr)(TO_PTR(pp))) + len)))) - 1;
                      while (pp < ppend)
                      {
                        if (p == *(pp)) return 1;
                        pp += 1;
                      }
                    }
                  }
                  else
                  {
                    while (mask != 0)
                    {
                      if (mask & 1)
                      {
                        if (p == *(pp)) return 1;
                      }
                      mask >>= 1;
                      pp += 1;
                    }
                  }
                }
              }
              else
              {
                if (p == RECORDDESCPM(rtd)) return 1;
                num = RECORDDESCPM(rtd);
                {
                  iptr index = (BIGLEN(num)) - 1;
                  bigit mask = (BIGIT(num, index)) >> 1;
                  INT bits = bigit_bits - 1;
                  while (1)
                  {
                    do
                    {
                      if (mask & 1)
                      {
                        if (p == *(pp)) return 1;
                      }
                      mask >>= 1;
                      pp += 1;
                      bits -= 1;
                    }
                    while (bits > 0);
                    if (index == 0)
                    {
                      break;
                    }
                    index -= 1;
                    mask = BIGIT(num, index);
                    bits = bigit_bits;
                  }
                }
              }
            }
          }
        }
      }
      else if (TYPEP(tf, mask_vector, type_vector))
      {
        uptr len = Svector_length(p);
        {
          uptr idx, p_len = len;
          ptr *p_p = &INITVECTIT(p, 0);
          for (idx = 0; idx < p_len; idx++)
          {
            if (p_p[idx] == p) return 1;
          }
        }
      }
      else if (TYPEP(tf, mask_stencil_vector, type_stencil_vector))
      {
        uptr len = Sstencil_vector_length(p);
        {
          uptr idx, p_len = len;
          ptr *p_p = &INITSTENVECTIT(p, 0);
          for (idx = 0; idx < p_len; idx++)
          {
            if (p_p[idx] == p) return 1;
          }
        }
      }
      else if (TYPEP(tf, mask_string, type_string))
      {
      }
      else if (TYPEP(tf, mask_fxvector, type_fxvector))
      {
      }
      else if (TYPEP(tf, mask_bytevector, type_bytevector))
      {
      }
      else if ((iptr)tf == type_tlc)
      {
      }
      else if (TYPEP(tf, mask_box, type_box))
      {
        if (p == INITBOXREF(p)) return 1;
      }
      else if ((iptr)tf == type_ratnum)
      {
      }
      else if ((iptr)tf == type_exactnum)
      {
      }
      else if ((iptr)tf == type_inexactnum)
      {
      }
      else if (TYPEP(tf, mask_bignum, type_bignum))
      {
      }
      else if (TYPEP(tf, mask_port, type_port))
      {
        if (p == PORTINFO(p)) return 1;
      }
      else if (TYPEP(tf, mask_code, type_code))
      {
        {
          ptr t = CODERELOC(p);
          {
            iptr m = (t
                      ? (RELOCSIZE(t))
                      : 0);
            {
              ptr oldco = (t
                           ? (RELOCCODE(t))
                           : 0);
              {
                iptr a = 0;
                {
                  iptr n = 0;
                  while (n < m)
                  {
                    {
                      uptr entry = RELOCIT(t, n);
                      uptr item_off = 0;
                      uptr code_off = 0;
                      n = n + 1;
                      if (RELOC_EXTENDED_FORMAT(entry))
                      {
                        item_off = RELOCIT(t, n);
                        n = n + 1;
                        code_off = RELOCIT(t, n);
                        n = n + 1;
                      }
                      else
                      {
                        item_off = RELOC_ITEM_OFFSET(entry);
                        code_off = RELOC_CODE_OFFSET(entry);
                      }
                      a = a + code_off;
                      {
                        ptr obj = S_get_code_obj(RELOC_TYPE(entry), oldco, a, item_off);
                        if (p == obj) return 1;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      else if ((iptr)tf == type_thread)
      {
      }
      else if ((iptr)tf == type_rtd_counts)
      {
      }
      else if ((iptr)tf == type_phantom)
      {
      }
      else
      {
        S_error_abort("self-test: illegal typed object type");
      }
    }
    else if (t == type_pair)
    {
      {
        ISPC p_at_spc = SPACE(p);
        if (p_at_spc == space_ephemeron)
        {
        }
        else if (p_at_spc == space_weakpair)
        {
          if (p == INITCDR(p)) return 1;
        }
        else
        {
          if (p == INITCAR(p)) return 1;
          if (p == INITCDR(p)) return 1;
        }
      }
    }
    else if (t == type_closure)
    {
      ptr code = CLOSCODE(p);
      if (p == code) return 1;
      if ((CODETYPE(code)) & (code_flag_continuation << code_flags_offset))
      {
      }
      else
      {
        uptr len = CODEFREE(code);
        {
          uptr idx, p_len = len;
          ptr *p_p = &CLOSIT(p, 0);
          for (idx = 0; idx < p_len; idx++)
          {
            if (p_p[idx] == p) return 1;
          }
        }
      }
    }
    else if (t == type_symbol)
    {
    }
    else if (t == type_flonum)
    {
    }
    else
    {
      S_error_abort("self-test: illegal type");
    }
  }
  return 0;
}

static void mark_typemod_data_object(ptr p, uptr p_sz, seginfo *si)
{
  if (!si->marked_mask) {
    find_room_voidp(space_data, target_generation, ptr_align(segment_bitmap_bytes), si->marked_mask);
    memset(si->marked_mask, 0, segment_bitmap_bytes);
  }
  si->marked_mask[segment_bitmap_byte(p)] |= segment_bitmap_bit(p);
  {
    uptr addr = (uptr)p;
    uptr seg = addr_get_segment(addr);
    uptr end_seg = addr_get_segment(addr + p_sz - 1);
    if (seg == end_seg) {
      si->marked_count += p_sz;
    } else {
      seginfo *mark_si;
      si->marked_count += ((uptr)build_ptr(seg+1,0)) - addr;
      seg++;
      while (seg < end_seg) {
        mark_si = SegInfo(seg);
        if (!fully_marked_mask) init_fully_marked_mask();
        mark_si->marked_mask = fully_marked_mask;
        mark_si->marked_count = segment_bitmap_bytes;
        seg++;
      }
      mark_si = SegInfo(end_seg);
      if (!mark_si->marked_mask) {
        find_room_voidp(space_data, target_generation, ptr_align(segment_bitmap_bytes), mark_si->marked_mask);
        memset(mark_si->marked_mask, 0, segment_bitmap_bytes);
      }
        /* no need to set a bit: just make sure `marked_mask` is non-NULL */
      mark_si->marked_count += addr + p_sz - (uptr)build_ptr(end_seg,0);
    }
  }
}

static void measure(ptr p)
{
  ITYPE t = TYPEBITS(p);
  if (t == type_typed_object)
  {
    ptr tf = TYPEFIELD(p);
    if (TYPEP(tf, mask_record, type_record))
    {
      { /* measure */
        ptr r_p = RECORDINSTTYPE(p);
        if (!IMMEDIATE(r_p))
          push_measure(r_p);
      }
      {
        ptr rtd = RECORDINSTTYPE(p);
        {
          uptr len = UNFIX((RECORDDESCSIZE(rtd)));
          {
            uptr p_sz = size_record_inst(len);
            measure_total += p_sz;
            {
              ptr num = RECORDDESCPM(rtd);
              ptr* pp = &(RECORDINSTIT(p, 0));
              if (Sfixnump(num))
              {
                {
                  uptr mask = ((uptr)(UNFIX(num))) >> 1;
                  if (mask == (((uptr)-1) >> 1))
                  {
                    {
                      ptr* ppend = ((ptr*)(TO_VOIDP((((uptr)(TO_PTR(pp))) + len)))) - 1;
                      while (pp < ppend)
                      {
                        { /* measure */
                          ptr r_p = *(pp);
                          if (!IMMEDIATE(r_p))
                            push_measure(r_p);
                        }
                        pp += 1;
                      }
                    }
                  }
                  else
                  {
                    while (mask != 0)
                    {
                      if (mask & 1)
                      {
                        { /* measure */
                          ptr r_p = *(pp);
                          if (!IMMEDIATE(r_p))
                            push_measure(r_p);
                        }
                      }
                      mask >>= 1;
                      pp += 1;
                    }
                  }
                }
              }
              else
              {
                {
                  iptr index = (BIGLEN(num)) - 1;
                  bigit mask = (BIGIT(num, index)) >> 1;
                  INT bits = bigit_bits - 1;
                  while (1)
                  {
                    do
                    {
                      if (mask & 1)
                      {
                        { /* measure */
                          ptr r_p = *(pp);
                          if (!IMMEDIATE(r_p))
                            push_measure(r_p);
                        }
                      }
                      mask >>= 1;
                      pp += 1;
                      bits -= 1;
                    }
                    while (bits > 0);
                    if (index == 0)
                    {
                      break;
                    }
                    index -= 1;
                    mask = BIGIT(num, index);
                    bits = bigit_bits;
                  }
                }
              }
            }
          }
        }
      }
    }
    else if (TYPEP(tf, mask_vector, type_vector))
    {
      uptr len = Svector_length(p);
      {
        uptr p_sz = size_vector(len);
        measure_total += p_sz;
        {
          uptr idx, p_len = len;
          ptr *p_p = &INITVECTIT(p, 0);
          for (idx = 0; idx < p_len; idx++)
          {
            { /* measure */
              ptr r_p = p_p[idx];
              if (!IMMEDIATE(r_p))
                push_measure(r_p);
            }
          }
        }
      }
    }
    else if (TYPEP(tf, mask_stencil_vector, type_stencil_vector))
    {
      uptr len = Sstencil_vector_length(p);
      {
        uptr p_sz = size_stencil_vector(len);
        measure_total += p_sz;
        {
          uptr idx, p_len = len;
          ptr *p_p = &INITSTENVECTIT(p, 0);
          for (idx = 0; idx < p_len; idx++)
          {
            { /* measure */
              ptr r_p = p_p[idx];
              if (!IMMEDIATE(r_p))
                push_measure(r_p);
            }
          }
        }
      }
    }
    else if (TYPEP(tf, mask_string, type_string))
    {
      uptr sz = size_string((Sstring_length(p)));
      {
        uptr p_sz = sz;
        measure_total += p_sz;
      }
    }
    else if (TYPEP(tf, mask_fxvector, type_fxvector))
    {
      uptr sz = size_fxvector((Sfxvector_length(p)));
      {
        uptr p_sz = sz;
        measure_total += p_sz;
      }
    }
    else if (TYPEP(tf, mask_bytevector, type_bytevector))
    {
      uptr sz = size_bytevector((Sbytevector_length(p)));
      {
        uptr p_sz = sz;
        measure_total += p_sz;
      }
    }
    else if ((iptr)tf == type_tlc)
    {
      uptr p_sz = size_tlc;
      measure_total += p_sz;
      { /* measure */
        ptr r_p = INITTLCHT(p);
        if (!IMMEDIATE(r_p))
          push_measure(r_p);
      }
      { /* measure */
        ptr r_p = INITTLCKEYVAL(p);
        if (!IMMEDIATE(r_p))
          push_measure(r_p);
      }
      { /* measure */
        ptr r_p = INITTLCNEXT(p);
        if (!IMMEDIATE(r_p))
          push_measure(r_p);
      }
    }
    else if (TYPEP(tf, mask_box, type_box))
    {
      uptr p_sz = size_box;
      measure_total += p_sz;
      { /* measure */
        ptr r_p = INITBOXREF(p);
        if (!IMMEDIATE(r_p))
          push_measure(r_p);
      }
    }
    else if ((iptr)tf == type_ratnum)
    {
      uptr p_sz = size_ratnum;
      measure_total += p_sz;
      { /* measure */
        ptr r_p = RATNUM(p);
        if (!IMMEDIATE(r_p))
          push_measure(r_p);
      }
      { /* measure */
        ptr r_p = RATDEN(p);
        if (!IMMEDIATE(r_p))
          push_measure(r_p);
      }
    }
    else if ((iptr)tf == type_exactnum)
    {
      uptr p_sz = size_exactnum;
      measure_total += p_sz;
      { /* measure */
        ptr r_p = EXACTNUM_REAL_PART(p);
        if (!IMMEDIATE(r_p))
          push_measure(r_p);
      }
      { /* measure */
        ptr r_p = EXACTNUM_IMAG_PART(p);
        if (!IMMEDIATE(r_p))
          push_measure(r_p);
      }
    }
    else if ((iptr)tf == type_inexactnum)
    {
      uptr p_sz = size_inexactnum;
      measure_total += p_sz;
    }
    else if (TYPEP(tf, mask_bignum, type_bignum))
    {
      uptr sz = size_bignum((BIGLEN(p)));
      {
        uptr p_sz = sz;
        measure_total += p_sz;
      }
    }
    else if (TYPEP(tf, mask_port, type_port))
    {
      uptr p_sz = size_port;
      measure_total += p_sz;
      { /* measure */
        ptr r_p = PORTHANDLER(p);
        if (!IMMEDIATE(r_p))
          push_measure(r_p);
      }
      { /* measure */
        ptr r_p = PORTINFO(p);
        if (!IMMEDIATE(r_p))
          push_measure(r_p);
      }
      { /* measure */
        ptr r_p = PORTNAME(p);
        if (!IMMEDIATE(r_p))
          push_measure(r_p);
      }
    }
    else if (TYPEP(tf, mask_code, type_code))
    {
      uptr len = CODELEN(p);
      {
        uptr p_sz = size_code(len);
        measure_total += p_sz;
        { /* measure */
          ptr r_p = CODENAME(p);
          if (!IMMEDIATE(r_p))
            push_measure(r_p);
        }
        { /* measure */
          ptr r_p = CODEARITYMASK(p);
          if (!IMMEDIATE(r_p))
            push_measure(r_p);
        }
        { /* measure */
          ptr r_p = CODEINFO(p);
          if (!IMMEDIATE(r_p))
            push_measure(r_p);
        }
        { /* measure */
          ptr r_p = CODEPINFOS(p);
          if (!IMMEDIATE(r_p))
            push_measure(r_p);
        }
        {
          ptr t = CODERELOC(p);
          {
            iptr m = (t
                      ? (RELOCSIZE(t))
                      : 0);
            {
              ptr oldco = (t
                           ? (RELOCCODE(t))
                           : 0);
              {
                iptr a = 0;
                {
                  iptr n = 0;
                  while (n < m)
                  {
                    {
                      uptr entry = RELOCIT(t, n);
                      uptr item_off = 0;
                      uptr code_off = 0;
                      n = n + 1;
                      if (RELOC_EXTENDED_FORMAT(entry))
                      {
                        item_off = RELOCIT(t, n);
                        n = n + 1;
                        code_off = RELOCIT(t, n);
                        n = n + 1;
                      }
                      else
                      {
                        item_off = RELOC_ITEM_OFFSET(entry);
                        code_off = RELOC_CODE_OFFSET(entry);
                      }
                      a = a + code_off;
                      {
                        ptr obj = S_get_code_obj(RELOC_TYPE(entry), oldco, a, item_off);
                        { /* measure */
                          ptr r_p = obj;
                          if (!IMMEDIATE(r_p))
                            push_measure(r_p);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    else if ((iptr)tf == type_thread)
    {
      uptr p_sz = size_thread;
      measure_total += p_sz;
      {
        ptr tc = (ptr)(THREADTC(p));
        if (tc != ((ptr)0))
        {
          measure_add_stack_size(SCHEMESTACK(tc), SCHEMESTACKSIZE(tc));
          STACKCACHE(tc) = Snil;
          { /* measure */
            ptr r_p = CCHAIN(tc);
            if (!IMMEDIATE(r_p))
              push_measure(r_p);
          }
          { /* measure */
            ptr r_p = STACKLINK(tc);
            if (!IMMEDIATE(r_p))
              push_measure(r_p);
          }
          { /* measure */
            ptr r_p = WINDERS(tc);
            if (!IMMEDIATE(r_p))
              push_measure(r_p);
          }
          { /* measure */
            ptr r_p = ATTACHMENTS(tc);
            if (!IMMEDIATE(r_p))
              push_measure(r_p);
          }
          {
            ptr xcp = FRAME(tc, 0);
            {
              iptr co = (ENTRYOFFSET(xcp)) + (((uptr)xcp) - ((uptr)(TO_PTR((ENTRYOFFSETADDR(xcp))))));
              {
                ptr c_p = (ptr)(((uptr)xcp) - co);
                { /* measure */
                  ptr r_p = c_p;
                  if (!IMMEDIATE(r_p))
                    push_measure(r_p);
                }
                {
                  uptr base = (uptr)(SCHEMESTACK(tc));
                  {
                    uptr fp = (uptr)(SFP(tc));
                    {
                      uptr ret = (uptr)(FRAME(tc, 0));
                      while (fp != base)
                      {
                        if (fp < base)
                        {
                          S_error_abort("sweep_stack(gc): malformed stack");
                        }
                        fp = fp - (ENTRYFRAMESIZE(ret));
                        {
                          ptr* pp = (ptr*)(TO_VOIDP(fp));
                          iptr oldret = ret;
                          ret = (iptr)(*(pp));
                          {
                            ptr xcp = *(pp);
                            {
                              iptr co = (ENTRYOFFSET(xcp)) + (((uptr)xcp) - ((uptr)(TO_PTR((ENTRYOFFSETADDR(xcp))))));
                              {
                                ptr c_p = (ptr)(((uptr)xcp) - co);
                                { /* measure */
                                  ptr r_p = c_p;
                                  if (!IMMEDIATE(r_p))
                                    push_measure(r_p);
                                }
                                {
                                  ptr num = ENTRYLIVEMASK(oldret);
                                  if (Sfixnump(num))
                                  {
                                    {
                                      uptr mask = UNFIX(num);
                                      while (mask != 0)
                                      {
                                        pp += 1;
                                        if (mask & 1)
                                        {
                                          { /* measure */
                                            ptr r_p = *(pp);
                                            if (!IMMEDIATE(r_p))
                                              push_measure(r_p);
                                          }
                                        }
                                        mask >>= 1;
                                      }
                                    }
                                  }
                                  else
                                  {
                                    { /* measure */
                                      ptr r_p = *((ENTRYNONCOMPACTLIVEMASKADDR(oldret)));
                                      if (!IMMEDIATE(r_p))
                                        push_measure(r_p);
                                    }
                                    {
                                      ptr num = ENTRYLIVEMASK(oldret);
                                      iptr index = BIGLEN(num);
                                      while (index != 0)
                                      {
                                        index -= 1;
                                        {
                                          INT bits = bigit_bits;
                                          bigit mask = BIGIT(num, index);
                                          while (bits > 0)
                                          {
                                            bits -= 1;
                                            pp += 1;
                                            if (mask & 1)
                                            {
                                              { /* measure */
                                                ptr r_p = *(pp);
                                                if (!IMMEDIATE(r_p))
                                                  push_measure(r_p);
                                              }
                                            }
                                            mask >>= 1;
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                      { /* measure */
                        ptr r_p = THREADNO(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = CURRENTINPUT(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = CURRENTOUTPUT(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = CURRENTERROR(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = SFD(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = CURRENTMSO(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = TARGETMACHINE(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = FXLENGTHBV(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = FXFIRSTBITSETBV(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = NULLIMMUTABLEVECTOR(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = NULLIMMUTABLEFXVECTOR(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = NULLIMMUTABLEBYTEVECTOR(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = NULLIMMUTABLESTRING(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = COMPILEPROFILE(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = SUBSETMODE(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = DEFAULTRECORDEQUALPROCEDURE(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = DEFAULTRECORDHASHPROCEDURE(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = COMPRESSFORMAT(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = COMPRESSLEVEL(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      { /* measure */
                        ptr r_p = PARAMETERS(tc);
                        if (!IMMEDIATE(r_p))
                          push_measure(r_p);
                      }
                      {
                        INT i = 0;
                        while (i < virtual_register_count)
                        {
                          { /* measure */
                            ptr r_p = VIRTREG(tc, i);
                            if (!IMMEDIATE(r_p))
                              push_measure(r_p);
                          }
                          i += 1;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    else if ((iptr)tf == type_rtd_counts)
    {
      uptr p_sz = size_rtd_counts;
      measure_total += p_sz;
    }
    else if ((iptr)tf == type_phantom)
    {
      uptr p_sz = size_phantom;
      measure_total += p_sz;
      measure_total += PHANTOMLEN(p);
    }
    else
    {
      S_error_abort("measure: illegal typed object type");
    }
  }
  else if (t == type_pair)
  {
    {
      ISPC p_at_spc = SPACE(p);
      if (p_at_spc == space_ephemeron)
      {
        uptr p_sz = size_ephemeron;
        measure_total += p_sz;
        add_ephemeron_to_pending_measure(p);
      }
      else if (p_at_spc == space_weakpair)
      {
        uptr p_sz = size_pair;
        measure_total += p_sz;
        { /* measure */
          ptr r_p = INITCDR(p);
          if (!IMMEDIATE(r_p))
            push_measure(r_p);
        }
      }
      else
      {
        uptr p_sz = size_pair;
        measure_total += p_sz;
        { /* measure */
          ptr r_p = INITCAR(p);
          if (!IMMEDIATE(r_p))
            push_measure(r_p);
        }
        { /* measure */
          ptr r_p = INITCDR(p);
          if (!IMMEDIATE(r_p))
            push_measure(r_p);
        }
      }
    }
  }
  else if (t == type_closure)
  {
    ptr code = CLOSCODE(p);
    { /* measure */
      ptr r_p = code;
      if (!IMMEDIATE(r_p))
        push_measure(r_p);
    }
    if ((CODETYPE(code)) & (code_flag_continuation << code_flags_offset))
    {
      uptr p_sz = size_continuation;
      measure_total += p_sz;
      { /* measure */
        ptr r_p = CONTWINDERS(p);
        if (!IMMEDIATE(r_p))
          push_measure(r_p);
      }
      { /* measure */
        ptr r_p = CONTATTACHMENTS(p);
        if (!IMMEDIATE(r_p))
          push_measure(r_p);
      }
      if ((CONTLENGTH(p)) == scaled_shot_1_shot_flag)
      {
      }
      else
      {
        { /* measure */
          ptr r_p = CONTLINK(p);
          if (!IMMEDIATE(r_p))
            push_measure(r_p);
        }
        {
          ptr xcp = CONTRET(p);
          {
            iptr co = (ENTRYOFFSET(xcp)) + (((uptr)xcp) - ((uptr)(TO_PTR((ENTRYOFFSETADDR(xcp))))));
            {
              ptr c_p = (ptr)(((uptr)xcp) - co);
              { /* measure */
                ptr r_p = c_p;
                if (!IMMEDIATE(r_p))
                  push_measure(r_p);
              }
              {
                uptr stack = (uptr)(CONTSTACK(p));
                {
                  uptr base = stack;
                  {
                    uptr fp = stack + (CONTCLENGTH(p));
                    {
                      uptr ret = (uptr)(CONTRET(p));
                      while (fp != base)
                      {
                        if (fp < base)
                        {
                          S_error_abort("sweep_stack(gc): malformed stack");
                        }
                        fp = fp - (ENTRYFRAMESIZE(ret));
                        {
                          ptr* pp = (ptr*)(TO_VOIDP(fp));
                          iptr oldret = ret;
                          ret = (iptr)(*(pp));
                          {
                            ptr xcp = *(pp);
                            {
                              iptr co = (ENTRYOFFSET(xcp)) + (((uptr)xcp) - ((uptr)(TO_PTR((ENTRYOFFSETADDR(xcp))))));
                              {
                                ptr c_p = (ptr)(((uptr)xcp) - co);
                                { /* measure */
                                  ptr r_p = c_p;
                                  if (!IMMEDIATE(r_p))
                                    push_measure(r_p);
                                }
                                {
                                  ptr num = ENTRYLIVEMASK(oldret);
                                  if (Sfixnump(num))
                                  {
                                    {
                                      uptr mask = UNFIX(num);
                                      while (mask != 0)
                                      {
                                        pp += 1;
                                        if (mask & 1)
                                        {
                                          { /* measure */
                                            ptr r_p = *(pp);
                                            if (!IMMEDIATE(r_p))
                                              push_measure(r_p);
                                          }
                                        }
                                        mask >>= 1;
                                      }
                                    }
                                  }
                                  else
                                  {
                                    { /* measure */
                                      ptr r_p = *((ENTRYNONCOMPACTLIVEMASKADDR(oldret)));
                                      if (!IMMEDIATE(r_p))
                                        push_measure(r_p);
                                    }
                                    {
                                      ptr num = ENTRYLIVEMASK(oldret);
                                      iptr index = BIGLEN(num);
                                      while (index != 0)
                                      {
                                        index -= 1;
                                        {
                                          INT bits = bigit_bits;
                                          bigit mask = BIGIT(num, index);
                                          while (bits > 0)
                                          {
                                            bits -= 1;
                                            pp += 1;
                                            if (mask & 1)
                                            {
                                              { /* measure */
                                                ptr r_p = *(pp);
                                                if (!IMMEDIATE(r_p))
                                                  push_measure(r_p);
                                              }
                                            }
                                            mask >>= 1;
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    else
    {
      uptr len = CODEFREE(code);
      {
        uptr p_sz = size_closure(len);
        measure_total += p_sz;
        {
          uptr idx, p_len = len;
          ptr *p_p = &CLOSIT(p, 0);
          for (idx = 0; idx < p_len; idx++)
          {
            { /* measure */
              ptr r_p = p_p[idx];
              if (!IMMEDIATE(r_p))
                push_measure(r_p);
            }
          }
        }
      }
    }
  }
  else if (t == type_symbol)
  {
    uptr p_sz = size_symbol;
    measure_total += p_sz;
    { /* measure */
      ptr r_p = INITSYMVAL(p);
      if (!IMMEDIATE(r_p))
        push_measure(r_p);
    }
    { /* measure */
      ptr r_p = INITSYMPLIST(p);
      if (!IMMEDIATE(r_p))
        push_measure(r_p);
    }
    { /* measure */
      ptr r_p = INITSYMNAME(p);
      if (!IMMEDIATE(r_p))
        push_measure(r_p);
    }
    { /* measure */
      ptr r_p = INITSYMSPLIST(p);
      if (!IMMEDIATE(r_p))
        push_measure(r_p);
    }
    { /* measure */
      ptr r_p = INITSYMHASH(p);
      if (!IMMEDIATE(r_p))
        push_measure(r_p);
    }
  }
  else if (t == type_flonum)
  {
    uptr p_sz = size_flonum;
    measure_total += p_sz;
  }
  else
  {
    S_error_abort("measure: illegal type");
  }
}

