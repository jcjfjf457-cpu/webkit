int FUN_ffffffff82447930(long param_1,uint param_2,uint param_3,long param_4,uint param_5)

{
  long *plVar1;
  int iVar2;
  int *piVar3;
  undefined8 *puVar4;
  undefined8 uVar5;
  int *piVar6;
  int *piVar7;
  long lVar8;
  undefined8 *in_GS_OFFSET;
  
  if (param_4 == 0) {
    piVar3 = (int *)0x0;
  }
  else {
    if (0xa0 < param_5) {
      iVar2 = 0x16;
      piVar3 = (int *)0x0;
      goto LAB_ffffffff824480e2;
    }
    piVar3 = (int *)FUN_ffffffff823a4220(0xa0,&DAT_ffffffff8374d570,0x101);
    if (piVar3 == (int *)0x0) {
      iVar2 = 0xc;
      piVar3 = (int *)0x0;
      goto LAB_ffffffff824480e2;
    }
    if ((param_3 & 0x30000000) != 0) {
      FUN_ffffffff82689710(*in_GS_OFFSET,"copyin",0);
      iVar2 = FUN_ffffffff824ddfe0(param_4,piVar3,(long)(int)param_5);
      if (iVar2 != 0) goto LAB_ffffffff824480e2;
    }
  }
  if ((int)param_2 < 0) {
LAB_ffffffff824479c7:
    lVar8 = 0;
  }
  else {
    FUN_ffffffff82491820
              (&DAT_ffffffff843a3c18,
               "W:\\Build\\J02650690\\sys\\freebsd\\sys\\net\\bnet_netcontrol.c",0x2b6);
    lVar8 = DAT_ffffffff843a44a0;
    if (DAT_ffffffff843a44a0 != 0) {
      do {
        if (*(ushort *)(lVar8 + 0x70) == param_2) goto LAB_ffffffff82447a60;
        plVar1 = (long *)(lVar8 + 0x18);
        lVar8 = *plVar1;
      } while (*plVar1 != 0);
      goto LAB_ffffffff824479c7;
    }
    lVar8 = 0;
  }
LAB_ffffffff82447a60:
  iVar2 = 0x16;
  if (piVar3 != (int *)0x0) {
    if ((int)param_3 < 0x20000002) {
      if ((int)param_3 < 0x101) {
        if (param_3 == 1) {
          if ((0xf < (int)param_5) && (lVar8 == 0)) {
            FUN_ffffffff824ddd30(piVar3,0x10);
            iVar2 = FUN_ffffffff824fa880(DAT_ffffffff8449d1c8);
            piVar3[1] = iVar2;
            iVar2 = (int)DAT_ffffffff83c572d8;
LAB_ffffffff82447ce1:
            *piVar3 = iVar2;
            iVar2 = 0;
          }
        }
        else if (param_3 == 2) {
          if ((0x27 < (int)param_5) && (lVar8 == 0)) {
            FUN_ffffffff82200ac0(&DAT_ffffffff843ff190,piVar3,0x28);
            iVar2 = *(int *)(*(long *)(param_1 + 8) + 0xb0);
            FUN_ffffffff8230e6a0
                      (&DAT_ffffffff843ff168,0,
                       "W:\\Build\\J02650690\\sys\\freebsd\\sys\\net\\bnet_netcontrol.c",0x1a0);
            for (puVar4 = DAT_ffffffff843ff188; puVar4 != (undefined8 *)0x0;
                puVar4 = (undefined8 *)*puVar4) {
              if (*(int *)(puVar4 + 2) == iVar2) {
                uVar5 = 0x1a3;
                goto LAB_ffffffff82448047;
              }
            }
            puVar4 = (undefined8 *)FUN_ffffffff823a4220(0x18,&DAT_ffffffff8374d570,0x101);
            if (puVar4 == (undefined8 *)0x0) {
              uVar5 = 0x1a9;
LAB_ffffffff82448047:
              FUN_ffffffff8230e950
                        (&DAT_ffffffff843ff168,0,
                         "W:\\Build\\J02650690\\sys\\freebsd\\sys\\net\\bnet_netcontrol.c",uVar5);
              goto LAB_ffffffff8244806f;
            }
            *(int *)(puVar4 + 2) = iVar2;
            *puVar4 = DAT_ffffffff843ff188;
            if (DAT_ffffffff843ff188 != (undefined8 *)0x0) {
              DAT_ffffffff843ff188[1] = puVar4;
            }
            iVar2 = 0;
            DAT_ffffffff843ff188 = puVar4;
            puVar4[1] = &DAT_ffffffff843ff188;
            *(byte *)(piVar3 + 2) = *(byte *)(piVar3 + 2) | 1;
            FUN_ffffffff8230e950
                      (&DAT_ffffffff843ff168,0,
                       "W:\\Build\\J02650690\\sys\\freebsd\\sys\\net\\bnet_netcontrol.c",0x1af);
          }
        }
        else if ((param_3 == 0x14) && (3 < (int)param_5)) {
          iVar2 = FUN_ffffffff82227b20();
          goto LAB_ffffffff82447ce1;
        }
      }
      else {
        switch(param_3) {
        case 0x10000002:
          if (0x1f < (int)param_5) {
            if (lVar8 != 0) {
              FUN_ffffffff8230e6a0
                        (lVar8 + 0x4c0,0,
                         "W:\\Build\\J02650690\\sys\\freebsd\\sys\\net\\bnet_netcontrol.c",0xf6);
            }
            puVar4 = &DAT_ffffffff843ff200;
            if (lVar8 != 0) {
              puVar4 = (undefined8 *)(lVar8 + 0x520);
            }
            if (((*(byte *)((long)puVar4 + 0x14) & 1) == 0) || (*(int *)(puVar4 + 2) != *piVar3)) {
              puVar4 = &DAT_ffffffff843ff220;
              if (lVar8 != 0) {
                puVar4 = (undefined8 *)(lVar8 + 0x540);
              }
              if (((*(byte *)((long)puVar4 + 0x14) & 1) != 0) && (*(int *)(puVar4 + 2) == *piVar3))
              goto LAB_ffffffff82447b47;
              iVar2 = 5;
              puVar4 = &DAT_ffffffff843ff240;
              if (lVar8 != 0) {
                puVar4 = (undefined8 *)(lVar8 + 0x560);
              }
              if (((*(byte *)((long)puVar4 + 0x14) & 1) != 0) && (*(int *)(puVar4 + 2) == *piVar3))
              goto LAB_ffffffff82447b47;
            }
            else {
LAB_ffffffff82447b47:
              iVar2 = 0;
              *(undefined8 *)(piVar3 + 4) = *puVar4;
              piVar3[6] = *(int *)(puVar4 + 3);
              *puVar4 = 0;
              *(undefined2 *)(puVar4[1] + 0x70) = 0;
            }
            if (lVar8 != 0) {
              FUN_ffffffff8230e950
                        (lVar8 + 0x4c0,0,
                         "W:\\Build\\J02650690\\sys\\freebsd\\sys\\net\\bnet_netcontrol.c",0x10c);
            }
          }
          break;
        case 0x10000003:
        case 0x10000004:
        case 0x10000005:
        case 0x10000006:
        case 0x10000007:
        case 0x10000008:
        case 0x10000009:
        case 0x1000000a:
        case 0x1000000b:
        case 0x1000000c:
        case 0x1000000d:
        case 0x1000000e:
        case 0x1000000f:
        case 0x10000010:
        case 0x10000011:
        case 0x10000013:
        case 0x10000014:
        case 0x10000015:
        case 0x10000016:
        case 0x10000017:
        case 0x10000018:
        case 0x10000019:
        case 0x1000001a:
        case 0x1000001b:
        case 0x1000001c:
        case 0x1000001d:
        case 0x1000001e:
        case 0x1000001f:
        case 0x10000020:
        case 0x10000021:
        case 0x10000022:
        case 0x10000023:
        case 0x10000024:
          break;
        case 0x10000012:
          if (0x9f < (int)param_5) {
            iVar2 = FUN_ffffffff82627290(param_1,piVar3);
          }
          break;
        case 0x10000025:
          if (0x1f < (int)param_5) {
            iVar2 = FUN_ffffffff82627500(param_1,piVar3);
          }
          break;
        case 0x10000026:
          if (0x87 < (int)param_5) {
            iVar2 = FUN_ffffffff826271c0(param_1,piVar3);
          }
          break;
        case 0x10000027:
          if ((0x1f < (int)param_5) && (lVar8 != 0)) {
            iVar2 = FUN_ffffffff82627650(param_1,lVar8,piVar3);
          }
          break;
        case 0x10000028:
          if (0x3f < (int)param_5) {
            iVar2 = FUN_ffffffff82627670(param_1,lVar8,piVar3);
          }
          break;
        default:
          if (param_3 == 0x101) {
            if ((0x3f < (int)param_5) && (lVar8 == 0)) {
              uVar5 = 0x40;
              piVar6 = piVar3;
              piVar7 = (int *)&DAT_ffffffff843ff1b8;
              goto LAB_ffffffff82448000;
            }
          }
          else if (((param_3 == 0x102) && (0xf < (int)param_5)) && (lVar8 == 0)) {
            FUN_ffffffff824ddd30(piVar3,0x10);
            FUN_ffffffff8223bb00(piVar3,piVar3 + 1);
            iVar2 = 0;
            if (DAT_ffffffff84309550 != 0) {
              *(byte *)(piVar3 + 2) = *(byte *)(piVar3 + 2) | 1;
            }
          }
        }
      }
    }
    else {
      piVar7 = piVar3;
      switch(param_3) {
      case 0x20000002:
        if (((0x27 < (int)param_5) && (lVar8 == 0)) && (piVar3[2] == 0)) {
          piVar6 = (int *)&DAT_ffffffff843ff190;
          uVar5 = 0x28;
LAB_ffffffff82448000:
          FUN_ffffffff82200ac0(piVar7,piVar6,uVar5);
          iVar2 = 0;
        }
        break;
      case 0x20000003:
        if (7 < (int)param_5) {
          iVar2 = FUN_ffffffff822229f0(param_1,lVar8,piVar3);
        }
        break;
      case 0x20000004:
      case 0x20000005:
      case 0x20000006:
      case 0x20000008:
      case 0x20000009:
      case 0x2000000a:
      case 0x2000000b:
      case 0x2000000c:
      case 0x2000000d:
      case 0x2000000e:
      case 0x2000000f:
      case 0x20000011:
      case 0x20000013:
      case 0x20000014:
      case 0x20000015:
      case 0x20000016:
      case 0x20000017:
      case 0x20000018:
      case 0x20000019:
      case 0x2000001a:
      case 0x2000001b:
      case 0x2000001c:
      case 0x2000001d:
      case 0x2000001e:
      case 0x2000001f:
      case 0x20000020:
      case 0x20000021:
      case 0x20000022:
      case 0x20000023:
      case 0x20000026:
        break;
      case 0x20000007:
        if (7 < (int)param_5) {
          iVar2 = FUN_ffffffff82222ac0(param_1,lVar8,piVar3);
        }
        break;
      case 0x20000010:
        if (lVar8 == 0) {
          iVar2 = 5;
        }
        else if (3 < (int)param_5) {
          if (*(char *)(lVar8 + 0xa4) == '\x02') {
            uVar5 = 4;
          }
          else {
            uVar5 = 8;
          }
          FUN_ffffffff82447200(lVar8,uVar5,0,0);
LAB_ffffffff8244806f:
          iVar2 = 0;
        }
        break;
      case 0x20000012:
        if (0x9f < (int)param_5) {
          iVar2 = FUN_ffffffff82625bb0(param_1,piVar3,0);
        }
        break;
      case 0x20000024:
        if ((0xb < (int)param_5) && (lVar8 == 0)) {
          iVar2 = FUN_ffffffff82222650(param_1,piVar3);
        }
        break;
      case 0x20000025:
        if (0x1f < (int)param_5) {
          iVar2 = FUN_ffffffff82626380(param_1,piVar3,0);
        }
        break;
      case 0x20000027:
        if ((0x1f < (int)param_5) && (lVar8 != 0)) {
          iVar2 = FUN_ffffffff82627600(param_1,lVar8,piVar3);
        }
        break;
      default:
        if ((((param_3 == 0x20000101) && (0x3f < (int)param_5)) && (lVar8 == 0)) && (piVar3[8] == 0)
           ) {
          piVar6 = (int *)&DAT_ffffffff843ff1b8;
          uVar5 = 0x40;
          goto LAB_ffffffff82448000;
        }
      }
    }
  }
  if (-1 < (int)param_2) {
    FUN_ffffffff82491a80
              (&DAT_ffffffff843a3c18,
               "W:\\Build\\J02650690\\sys\\freebsd\\sys\\net\\bnet_netcontrol.c",0x2bf);
  }
  if (((param_4 != 0) && (iVar2 == 0)) && (iVar2 = 0, (param_3 & 0x30000000) != 0x20000000)) {
    FUN_ffffffff82689710(*in_GS_OFFSET,"copyout",0);
    iVar2 = FUN_ffffffff824ddef0(piVar3,param_4,(long)(int)param_5);
  }
LAB_ffffffff824480e2:
  FUN_ffffffff823a43e0(piVar3,&DAT_ffffffff8374d570);
  return iVar2;
}