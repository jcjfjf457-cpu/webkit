undefined4 FUN_ffffffff82507d40(long param_1,undefined8 param_2,uint param_3,undefined8 param_4)

{
  int *piVar1;
  uint *puVar2;
  uint *puVar3;
  long lVar4;
  ulong uVar5;
  int iVar6;
  int iVar7;
  undefined4 uVar8;
  ulong uVar9;
  short *psVar10;
  undefined4 *puVar11;
  undefined8 uVar12;
  uint uVar13;
  uint uVar14;
  undefined8 uVar15;
  uint uVar16;
  undefined4 *puVar17;
  undefined4 *puVar18;
  long lVar19;
  undefined8 *in_GS_OFFSET;
  undefined *puStack_b0;
  undefined4 auStack_a8 [2];
  undefined8 local_a0;
  long local_98;
  ulong local_90;
  undefined8 local_88;
  uint *local_80;
  long local_78;
  undefined8 local_70;
  uint *local_68;
  undefined8 local_60;
  undefined4 *local_58;
  short *local_50;
  undefined4 local_48;
  undefined4 local_44;
  undefined8 local_40;
  long local_38;
  
  puVar17 = auStack_a8;
  local_38 = DAT_ffffffff84948f40;
  lVar19 = *(long *)(param_1 + 8);
  local_88 = *(undefined8 *)(lVar19 + 0xab8);
  local_44 = 0;
  local_48 = 0;
  iVar6 = -(uint)(DAT_ffffffff8449d988 != lVar19);
  if (*(int *)(lVar19 + 0xaf4) != -1) {
    iVar6 = *(int *)(lVar19 + 0xaf4);
  }
  if ((&DAT_ffffffff8449d980)[(ulong)(iVar6 != 0) * 0x166] != 1) {
    puStack_b0 = (undefined *)0xffffffff82507dcc;
    iVar6 = FUN_ffffffff8250b8a0(1,&DAT_ffffffff8449d4e0 + (ulong)(iVar6 != 0) * 0x598);
    if (iVar6 != 0) {
      uVar12 = 0xe5f;
      goto LAB_ffffffff82507e1a;
    }
  }
  if (param_3 - 1 < 0x80) {
    local_a0 = param_4;
    if ((int)param_3 < 2) {
      puVar11 = &local_44;
      puVar18 = &local_48;
      lVar19 = 4;
      local_90 = 1;
    }
    else {
      local_90 = (ulong)param_3;
      lVar19 = local_90 * 4;
      uVar9 = local_90 * 4 + 0xf & 0xfffffffffffffff0;
      puVar11 = (undefined4 *)((long)auStack_a8 - uVar9);
      puVar17 = (undefined4 *)((long)puVar11 - uVar9);
      *(undefined8 *)(puVar17 + -2) = 0xffffffff82507e71;
      FUN_ffffffff824ddd30(puVar17,lVar19);
      puVar18 = puVar17;
    }
    uVar12 = *in_GS_OFFSET;
    *(undefined8 *)(puVar17 + -2) = 0xffffffff82507ea7;
    FUN_ffffffff82689710(uVar12,"copyin",0);
    *(undefined8 *)(puVar17 + -2) = 0xffffffff82507eb5;
    psVar10 = (short *)FUN_ffffffff824ddfe0(param_2,puVar11,lVar19);
    if ((int)psVar10 != 0) {
                    /* WARNING: Subroutine does not return */
      *(undefined **)(puVar17 + -2) = &UNK_ffffffff82507eda;
      FUN_ffffffff824fcbd0
                ("%s() line=%d error=%d 0x%x\n","_aio_multi_delete",0xe74,
                 (ulong)psVar10 & 0xffffffff,(ulong)psVar10 & 0xffffffff);
    }
    uVar9 = 0;
    uVar14 = 0;
    local_60 = (ulong)local_60._4_4_ << 0x20;
    local_98 = lVar19;
    local_70 = uVar12;
    local_58 = puVar11;
    do {
      uVar13 = puVar11[uVar9];
      puVar18[uVar9] = 0;
      uVar12 = local_40;
      if ((uVar13 < 0x800000) && (uVar16 = uVar13 & 0xffff, uVar16 != 0)) {
        if (uVar16 != uVar14) {
          if ((int)local_60 != 0) {
            *(undefined8 *)(puVar17 + -2) = 0xffffffff82507f4c;
            FUN_ffffffff8251dc80(uVar12);
          }
          uVar12 = local_88;
          *(undefined8 *)(puVar17 + -2) = 0xffffffff82507f61;
          psVar10 = (short *)FUN_ffffffff8251dcc0(uVar12,uVar16,0x160,&local_40);
          if (psVar10 == (short *)0x0) {
            puVar18[uVar9] = 0x80020003;
            local_60 = (ulong)local_60._4_4_ << 0x20;
            psVar10 = (short *)0x0;
            puVar11 = local_58;
            uVar14 = 0;
            goto LAB_ffffffff82507f09;
          }
          local_60 = CONCAT44(local_60._4_4_,1);
        }
        uVar12 = local_40;
        if (psVar10 == (short *)0x0) {
          puVar18[uVar9] = 0x80020003;
                    /* WARNING: Subroutine does not return */
          *(undefined **)(puVar17 + -2) = &UNK_ffffffff82507fea;
          FUN_ffffffff824fcbd0
                    ("[0]%s() line=%d i=%d err=0x%x\n","_aio_multi_delete",0xea1,uVar9 & 0xffffffff,
                     3);
        }
        iVar6 = (int)uVar13 >> 0x10;
        local_50 = psVar10;
        if (*psVar10 <= iVar6) {
          uVar12 = 0xeaa;
          uVar15 = 3;
          puVar18[uVar9] = 0x80020003;
LAB_ffffffff82508016:
                    /* WARNING: Subroutine does not return */
          *(undefined8 *)(puVar17 + -2) = 0xffffffff8250801d;
          FUN_ffffffff824fcbd0
                    ("[0]%s() line=%d i=%d err=0x%x\n","_aio_multi_delete",uVar12,uVar9 & 0xffffffff
                     ,uVar15);
        }
        *(undefined8 *)(puVar17 + -2) = 0xffffffff82507f8f;
        iVar7 = FUN_ffffffff8251d4f0(uVar12);
        if (iVar7 != 0) {
          puVar18[uVar9] = 0x80020001;
          uVar12 = 0xeb0;
          uVar15 = 1;
          goto LAB_ffffffff82508016;
        }
        lVar19 = *(long *)(*(long *)(local_50 + 0x14) + (long)iVar6 * 8);
        if (lVar19 == 0) {
          puVar18[uVar9] = 0x80020003;
                    /* WARNING: Subroutine does not return */
          *(undefined **)(puVar17 + -2) = &UNK_ffffffff8250818e;
          FUN_ffffffff824fcbd0
                    ("[0]%s() line=%d i=%d err=0x%x\n","_aio_multi_delete",0xeb7,uVar9 & 0xffffffff,
                     3);
        }
        puVar2 = *(uint **)(lVar19 + 0x20);
        uVar14 = uVar16;
        if (puVar2[2] - 3 < 2) {
          local_80 = puVar2 + 8;
          local_78 = (long)iVar6;
          *(undefined8 *)(puVar17 + -2) = 0xece;
          *(char **)(puVar17 + -4) = "W:\\Build\\J02650690\\sys\\freebsd\\sys\\kern\\vfs_aio2.c";
          *(undefined8 *)(puVar17 + -6) = 0xffffffff8250809e;
          FUN_ffffffff823ab8f0(puVar2 + 8,0x80000,0,0,0,0);
          puVar3 = local_80;
          if ((char)puVar2[3] == '\0') {
                    /* WARNING: Subroutine does not return */
            *(undefined **)(puVar17 + -2) = &UNK_ffffffff825080cd;
            FUN_ffffffff824fcbd0("%s() line=%d error=%d 0x%x\n","_aio_multi_delete",0xed1,0x10,0x10)
            ;
          }
          local_68 = puVar2;
          if (*(long *)(puVar2 + 0x14) != 0) {
                    /* WARNING: Subroutine does not return */
            *(undefined **)(puVar17 + -2) = &UNK_ffffffff82508106;
            FUN_ffffffff824fcbd0("%s() line=%d error=%d 0x%x\n","_aio_multi_delete",0xed6,0x10,0x10)
            ;
          }
          *(undefined8 *)(puVar17 + -2) = 0xeda;
          *(char **)(puVar17 + -4) = "W:\\Build\\J02650690\\sys\\freebsd\\sys\\kern\\vfs_aio2.c";
          *(undefined8 *)(puVar17 + -6) = 0xffffffff82508134;
          FUN_ffffffff823ab8f0(puVar3,0x100000,0,0,0,0);
          uVar15 = local_40;
          psVar10 = local_50;
          puVar2 = local_80;
          uVar12 = local_88;
          puVar11 = local_58;
          if (((puVar18[uVar9] == 0) && (local_68[1] == 0)) && ((char)local_68[3] != '\0')) {
            if (local_50[1] == 1) {
              *(undefined8 *)(puVar17 + -2) = 0xffffffff825081c6;
              FUN_ffffffff8251dc80(uVar15);
              *(undefined8 *)(puVar17 + -2) = 0xffffffff825081da;
              psVar10 = (short *)FUN_ffffffff8251e2c0(uVar12,uVar16,0x160,&local_40);
              uVar15 = local_40;
              if (psVar10 == (short *)0x0) {
                puVar18[uVar9] = 0;
                puVar11 = local_58;
                uVar14 = 0;
              }
              else {
                local_50 = psVar10;
                *(undefined8 *)(puVar17 + -2) = 0xffffffff825081f6;
                FUN_ffffffff8251dbf0(uVar12,uVar16,uVar15);
                uVar12 = local_40;
                *(undefined8 *)(puVar17 + -2) = 0xffffffff825081ff;
                FUN_ffffffff8251dc80(uVar12);
                uVar12 = local_70;
                local_60 = *(ulong *)(lVar19 + 0x18);
                if (*local_50 == 1) {
                  uVar14 = *local_68;
                  if (uVar14 != 0) {
                    uVar13 = 0;
                    psVar10 = local_50;
                    do {
                      uVar12 = local_70;
                      lVar19 = *(long *)(*(long *)(psVar10 + 0x14) + (long)(int)uVar13 * 8);
                      if (lVar19 != 0) {
                        if (*(long *)(lVar19 + 0x28) != 0) {
                    /* WARNING: Subroutine does not return */
                          *(undefined8 *)(puVar17 + -2) = 0xffffffff8250828f;
                          FUN_ffffffff824fcbd0
                                    ("[0]%s() line=%d Warning !! split info is here\n",
                                     "free_queue_entry",0xb28);
                        }
                        if (*(long *)(lVar19 + 0x40) != 0) {
                          LOCK();
                          piVar1 = (int *)(*(long *)(lVar19 + 0x40) + 0x28);
                          iVar6 = *piVar1;
                          *piVar1 = *piVar1 + -1;
                          UNLOCK();
                          if (iVar6 == 1) {
                            uVar15 = *(undefined8 *)(lVar19 + 0x40);
                            *(undefined8 *)(puVar17 + -2) = 0xffffffff825082b4;
                            FUN_ffffffff826161b0(uVar15,uVar12);
                          }
                          *(undefined8 *)(lVar19 + 0x40) = 0;
                        }
                        *(undefined8 *)(puVar17 + -2) = 0xffffffff8250823e;
                        FUN_ffffffff823a43e0(lVar19,&DAT_ffffffff83c59230);
                        *(undefined8 *)(*(long *)(local_50 + 0x14) + (long)(int)uVar13 * 8) = 0;
                        uVar14 = *local_68;
                        psVar10 = local_50;
                      }
                      uVar13 = uVar13 + 1;
                    } while (uVar13 < uVar14);
                  }
                }
                else {
                  lVar19 = *(long *)(*(long *)(local_50 + 0x14) + local_78 * 8);
                  if (*(long *)(lVar19 + 0x28) != 0) {
                    /* WARNING: Subroutine does not return */
                    *(undefined8 *)(puVar17 + -2) = 0xffffffff8250838a;
                    FUN_ffffffff824fcbd0
                              ("[0]%s() line=%d Warning !! split info is here\n","free_queue_entry",
                               0xb28);
                  }
                  if (*(long *)(lVar19 + 0x40) != 0) {
                    LOCK();
                    piVar1 = (int *)(*(long *)(lVar19 + 0x40) + 0x28);
                    iVar6 = *piVar1;
                    *piVar1 = *piVar1 + -1;
                    UNLOCK();
                    if (iVar6 == 1) {
                      uVar15 = *(undefined8 *)(lVar19 + 0x40);
                      *(undefined8 *)(puVar17 + -2) = 0xffffffff825083ae;
                      FUN_ffffffff826161b0(uVar15,uVar12);
                    }
                    *(undefined8 *)(lVar19 + 0x40) = 0;
                  }
                  *(undefined8 *)(puVar17 + -2) = 0xffffffff825083c5;
                  FUN_ffffffff823a43e0(lVar19,&DAT_ffffffff83c59230);
                }
                uVar5 = local_60;
                uVar12 = *(undefined8 *)(local_60 + 0x10);
                *(undefined8 *)(puVar17 + -2) = 0xffffffff825083d2;
                FUN_ffffffff82631950(uVar12);
                *(undefined8 *)(puVar17 + -2) = 0xffffffff825083e1;
                FUN_ffffffff823a43e0(uVar5,&DAT_ffffffff83c592d0);
                puVar2 = local_80;
                *(undefined8 *)(*(long *)(local_50 + 0x14) + local_78 * 8) = 0;
                if (1 < *local_68) {
                  uVar14 = 0;
                  do {
                    if (*(long *)(*(long *)(local_50 + 0x14) + (long)(int)uVar14 * 8) != 0) {
                    /* WARNING: Subroutine does not return */
                      *(undefined **)(puVar17 + -2) = &UNK_ffffffff82508440;
                      FUN_ffffffff824fcbd0
                                ("[0]%s() line=%d [%d] aio_obj->queue_ent[%d]=%p\n",
                                 "_aio_multi_delete",0xf11,uVar14,uVar14);
                    }
                    uVar14 = uVar14 + 1;
                  } while (uVar14 < *local_68);
                }
                *(undefined8 *)(puVar17 + -2) = 0xffffffff82508454;
                FUN_ffffffff823ab8e0(puVar2);
                uVar12 = *(undefined8 *)(local_50 + 8);
                *(undefined8 *)(puVar17 + -2) = 0xffffffff82508468;
                FUN_ffffffff823a43e0(uVar12,&DAT_ffffffff83c59280);
                uVar12 = *(undefined8 *)(local_50 + 0x10);
                *(undefined8 *)(puVar17 + -2) = 0xffffffff8250847c;
                FUN_ffffffff823a43e0(uVar12,&DAT_ffffffff83c591e0);
                uVar12 = *(undefined8 *)(local_50 + 0x14);
                *(undefined8 *)(puVar17 + -2) = 0xffffffff82508493;
                FUN_ffffffff823a43e0(uVar12,&DAT_ffffffff83c59320);
                psVar10 = local_50;
                *(undefined8 *)(puVar17 + -2) = 0xffffffff8250849f;
                FUN_ffffffff823a43e0(psVar10,&DAT_ffffffff83c59320);
                local_60 = local_60 & 0xffffffff00000000;
                psVar10 = local_50;
                puVar11 = local_58;
                uVar14 = 0;
              }
            }
            else {
              local_50[1] = local_50[1] + -1;
              *(undefined8 *)(puVar17 + -2) = 0xffffffff825082cb;
              FUN_ffffffff823ab8e0(puVar2);
              uVar12 = local_70;
              lVar4 = local_78;
              lVar19 = *(long *)(*(long *)(psVar10 + 0x14) + local_78 * 8);
              if (*(long *)(lVar19 + 0x28) != 0) {
                    /* WARNING: Subroutine does not return */
                *(undefined8 *)(puVar17 + -2) = 0xffffffff825082f8;
                FUN_ffffffff824fcbd0
                          ("[0]%s() line=%d Warning !! split info is here\n","free_queue_entry",
                           0xb28);
              }
              if (*(long *)(lVar19 + 0x40) != 0) {
                LOCK();
                piVar1 = (int *)(*(long *)(lVar19 + 0x40) + 0x28);
                iVar6 = *piVar1;
                *piVar1 = *piVar1 + -1;
                UNLOCK();
                if (iVar6 == 1) {
                  uVar15 = *(undefined8 *)(lVar19 + 0x40);
                  *(undefined8 *)(puVar17 + -2) = 0xffffffff8250831d;
                  FUN_ffffffff826161b0(uVar15,uVar12);
                }
                *(undefined8 *)(lVar19 + 0x40) = 0;
              }
              *(undefined8 *)(puVar17 + -2) = 0xffffffff82508334;
              FUN_ffffffff823a43e0(lVar19,&DAT_ffffffff83c59230);
              *(undefined8 *)(*(long *)(local_50 + 0x14) + lVar4 * 8) = 0;
              psVar10 = local_50;
              puVar11 = local_58;
            }
          }
        }
        else {
          puVar18[uVar9] = 0x80020010;
          psVar10 = local_50;
          puVar11 = local_58;
        }
      }
      else {
        puVar18[uVar9] = 0x80020003;
      }
LAB_ffffffff82507f09:
      uVar9 = uVar9 + 1;
      if (uVar9 == local_90) {
        if ((int)local_60 != 0) {
          *(undefined8 *)(puVar17 + -2) = 0xffffffff825084c0;
          FUN_ffffffff8251dc80(local_40);
        }
        uVar12 = local_70;
        *(undefined8 *)(puVar17 + -2) = 0xffffffff825084d2;
        FUN_ffffffff82689710(uVar12,"copyout",0);
        lVar19 = local_98;
        uVar12 = local_a0;
        *(undefined8 *)(puVar17 + -2) = 0xffffffff825084e8;
        uVar8 = FUN_ffffffff824ddef0(puVar18,uVar12,lVar19);
        if (DAT_ffffffff84948f40 != local_38) {
                    /* WARNING: Subroutine does not return */
          *(undefined **)(puVar17 + -2) = &UNK_ffffffff82508511;
          FUN_ffffffff828c6f80();
        }
        return uVar8;
      }
    } while( true );
  }
  uVar12 = 0xe65;
  iVar6 = 0x16;
LAB_ffffffff82507e1a:
                    /* WARNING: Subroutine does not return */
  puStack_b0 = &UNK_ffffffff82507e21;
  FUN_ffffffff824fcbd0("%s() line=%d error=%d 0x%x\n","_aio_multi_delete",uVar12,iVar6,iVar6);
}
