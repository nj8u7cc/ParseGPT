#!/usr/bin/python
#===========================================================================

#  This script parses "partition.xml" and creates numerous output files
#  specifically, partition.bin, rawprogram.xml

#  $DateTime: 2015/09/16 19:44:13 $
#  $Author: Nuc $

# All Rights Reserved.
# ===========================================================================*/

import sys
import os
import math
import re
import struct
import string
from types import *
from os.path import join, getsize

from xml.etree import ElementTree as ET
from xml.etree.ElementTree import ElementTree
from xml.etree.ElementTree import Element
from xml.etree.ElementTree import SubElement
from xml.etree.ElementTree import dump
from xml.etree.ElementTree import Comment
from xml.etree.ElementTree import tostring
from xml.dom import minidom

if sys.version_info < (2,5):
    sys.stdout.write("\n\nERROR: This script needs Python version 2.5 or greater, detected as ")
    print sys.version_info
    sys.exit()  # error



class partition:
    def __init__(self):
        self.typeGUID = 0x00000000000000000000000000000000
        self.GUID = 0x00000000000000000000000000000000
        self.SECTOR_SIZE_IN_BYTES = 512
        self.file_sector_offset = 0
        self.filename = ''
        self.label = ''
        self.num_partition_sectors = 0
        self.partofsingleimage = 'false'
        self.physical_partition_number = 0
        self.readbackverify = 'false'
        self.size_in_KB = 0
        self.sparse = 'false'
        self.start_byte_hex = 0x00
        self.start_sector = 0
        self.end_sector = 0
        self.attr = 0



PrimaryGPT = [0]*34*512  # This is LBA 0 to 33 (34 sectors total)    (start of disk)
BackupGPT = [0xFF]*33*512  # This is LBA -33 to -1 (33 sectors total)   (end of disk)
GPTHeader = {}
GPTContent = {}
CurrentLBA = 0
BackupLBA = 0
SectorSize = 512
NUM_DISK_SECTORS = 30777344  #16Gb eMMC
PhyPartitionStartSector = 0
PhyPartitionEndSector = 0
NumPhyPartitions = 0
PartitionCollection = {}        # An array of Partition objects. Partition is a hash of information about partition



LastPartitionBeginsAt = 0
HashInstructions       = {}


MinSectorsNeeded        = 0
# Ex. PhyPartition[0] holds the PartitionCollection that holds all the info for partitions in PHY partition 0

AvailablePartitions = {}
XMLFile = "module_common.py"

ExtendedPartitionBegins= 0
instructions           = []
HashStruct             = {}

StructPartitions       = []
StructAdditionalFields = []
AllPartitions          = {}

PARTITION_SYSTEM_GUID       =  0x3BC93EC9A0004BBA11D2F81FC12A7328
PARTITION_MSFT_RESERVED_GUID=  0xAE1502F02DF97D814DB80B5CE3C9E316
PARTITION_BASIC_DATA_GUID   =  0xC79926B7B668C0874433B9E5EBD0A0A2



## Note that these HashInstructions are updated by the XML file

HashInstructions['WRITE_PROTECT_BOUNDARY_IN_KB']        = 64*1024
HashInstructions['GROW_LAST_PARTITION_TO_FILL_DISK']    = True
HashInstructions['DISK_SIGNATURE']                      = 0x0

MBR         = [0]*512
EBR         = [0]*512

hash_w       = [{'start_sector':0,'num_sectors':(HashInstructions['WRITE_PROTECT_BOUNDARY_IN_KB']*1024/512),
                 'end_sector':(HashInstructions['WRITE_PROTECT_BOUNDARY_IN_KB']*1024/512)-1,'physical_partition_number':0,'boundary_num':0,'num_boundaries_covered':1}]
NumWPregions = 0


def UpdatePatch(StartSector,ByteOffset,PHYPartition,size_in_bytes,szvalue,szfilename,szwhat):

    SubElement(PatchesXML, 'patch', {'start_sector':StartSector, 'byte_offset':ByteOffset,
                                     'physical_partition_number':str(PHYPartition), 'size_in_bytes':str(size_in_bytes),
                                     'value':szvalue, 'filename':szfilename, 'what':szwhat   })



def ValidateGUID(GUID):
    m = re.search("0x([a-fA-F\d]+)$", GUID)     #0xC79926B7B668C0874433B9E5EBD0A0A2
    if type(m) is not NoneType:
        tempGUID = int(m.group(1),16)
        print "\tGUID \"%s\"" % GUID

        if tempGUID == PARTITION_SYSTEM_GUID:
            print "\tPARTITION_SYSTEM_GUID detected"
        elif tempGUID == PARTITION_MSFT_RESERVED_GUID:
            print "\tPARTITION_MSFT_RESERVED_GUID detected"
        elif tempGUID == PARTITION_BASIC_DATA_GUID:
            print "\tPARTITION_BASIC_DATA_GUID detected"
        else:
            print "\tUNKNOWN PARTITION_GUID detected"

        return tempGUID

    else:
        #ebd0a0a2-b9e5-4433-87c0-68b6b72699c7  --> #0x C7 99 26 B7 B6 68 C087 4433 B9E5 EBD0A0A2
        m = re.search("([a-fA-F\d]{8})-([a-fA-F\d]{4})-([a-fA-F\d]{4})-([a-fA-F\d]{2})([a-fA-F\d]{2})-([a-fA-F\d]{2})([a-fA-F\d]{2})([a-fA-F\d]{2})([a-fA-F\d]{2})([a-fA-F\d]{2})([a-fA-F\d]{2})", GUID)
        if type(m) is not NoneType:
            tempGUID = (int(m.group(4),16)<<64) | (int(m.group(3),16)<<48) | (int(m.group(2),16)<<32) | int(m.group(1),16)
            tempGUID|= (int(m.group(8),16)<<96) | (int(m.group(7),16)<<88) | (int(m.group(6),16)<<80) | (int(m.group(5),16)<<72)
            tempGUID|= (int(m.group(11),16)<<120)| (int(m.group(10),16)<<112)| (int(m.group(9),16)<<104)
            print "GUID \"%s\" is FOUND --> 0x%X" % (GUID,tempGUID)
            return tempGUID
        else:
            print "GUID \"%s\" is not in the form ebd0a0a2-b9e5-4433-87c0-68b6b72699c7" % GUID
            print "Converted to PARTITION_BASIC_DATA_GUID (0xC79926B7B668C0874433B9E5EBD0A0A2)"
            return PARTITION_BASIC_DATA_GUID



def WriteGPT(k):
    global opfile,PrimaryGPT,BackupGPT

    opfile = open("gpt_main%d.bin" % k, "wb")
    for b in PrimaryGPT:
        opfile.write(struct.pack("B", b))
    opfile.close()
    print "Created \"gpt_main%d.bin\" length = %d byte" % (k,len(PrimaryGPT))

    opfile = open("gpt_backup%d.bin" % k, "wb")
    for b in BackupGPT:
        opfile.write(struct.pack("B", b))
    opfile.close()
    print "Created \"gpt_backup%d.bin\" length = %d byte" % (k,len(BackupGPT))


def UpdatePrimaryGPT(value,length,i):
    global PrimaryGPT
    for b in range(length):
        PrimaryGPT[i] = ((value>>(b*8)) & 0xFF) ; i+=1
    return i

def UpdateBackupGPT(value,length,i):
    global BackupGPT
    for b in range(length):
        BackupGPT[i] = ((value>>(b*8)) & 0xFF) ; i+=1
    return i

def ShowBackupGPT(sector):
    global BackupGPT
    print "Sector: %d" % sector
    for j in range(32):
        for i in range(16):
            sys.stdout.write("%.2X " % BackupGPT[i+j*16+sector*512])
        print " "
    print " "


def AlignVariablesToEqualSigns(sz):
    temp = re.sub("(\t| )+=","=",sz)
    temp = re.sub("=(\t| )+","=",temp)
    return temp

def ReturnArrayFromSpaceSeparatedList(sz):
    temp = re.sub("\s+|\n"," ",sz)
    temp = re.sub("^\s+","",temp)
    temp = re.sub("\s+$","",temp)
    return temp.split(' ')

def ParseXML(XMLFile):
    global NumPhyPartitions, PartitionCollection, PhyPartition,MinSectorsNeeded

    root = ET.parse( XMLFile )

    #Create an iterator
    iter = root.getiterator()

    for element in iter:
        #print "\nElement:" , element.tag   # thins like image,primary,extended etc

        if element.tag=="parser_instructions":
            instructions = ReturnArrayFromSpaceSeparatedList(AlignVariablesToEqualSigns(element.text))

            for element in instructions:
                temp = element.split('=')
                if len(temp) > 1:
                    HashInstructions[temp[0].strip()] = temp[1].strip()
                    #print "HashInstructions['%s'] = %s" % (temp[0].strip(),temp[1].strip())

        elif element.tag=="physical_partition":
            ## Legacy approach
            #<physical_partition number="0">
            #    <primary order="3" type="B" bootable="false" label="OEMSBL" size="2040256" readonly="true" emmcbld_req = "true">
            #        <file name="osbl.mbn" offset="0"/>
            #    </primary>

            # New approach
            #<physical_partition>
            #    <partition label="FAT" size_in_kb="1000" type="4c" bootable="false" readonly="false">
            #        <file name="oemsblhd.mbn" offset="0"/>
            #    </partition>

            ## print "\nFound a physical_partition, NumPhyPartitions=%d" % NumPhyPartitions

            NumPhyPartitions            += 1
            PartitionCollection          = []    # Reset, we've found a new physical partition

        elif element.tag=="partition" or element.tag=="primary" or element.tag=="extended":

            if element.keys():
                #print "\tAttributes:"

                # Reset all variables to defaults
                Partition = {}

                # This partition could have more than 1 file, so these are arrays
                # However, as I loop through the elements, *if* there is more than 1 file
                # it will have it's own <file> tag
                Partition['filename']           = [""]
                Partition['fileoffset']         = [0]
                Partition['appsbin']            = ["false"]
                Partition['filepartitionoffset']= [0]

                Partition['size_in_kb'] = 0
                Partition["readonly"]   = "false"
                #Partition['appsbin']    = "false"
                Partition['label']      = "false"
                Partition['type']       = "false"
                Partition['readonly']   = "false"
                Partition['align']      = "false"

                FileFound = 0

                for name, value in element.items():
                    #print "\t\tName: '%s'=>'%s' " % (name,value)

                    if name=='name' or name=='filename' :
                        Partition['filename'][-1] = value
                        FileFound = 1
                        print "Found a file, NumPhyPartitions=",NumPhyPartitions    ## i.e. just a file tag (usually in legacy)
                        print "Current partition is \"%s\"\n" % Partition['label']
                    elif name=='fileoffset':
                        Partition['fileoffset'][-1] = value
                    elif name=='offset' or name=='filepartitionoffset':
                        Partition['filepartitionoffset'][-1] = int(value)
                    elif name=='appsbin':
                        Partition['appsbin'][-1] = value
                    elif name=="size":
                        Partition["size_in_kb"]=int(value)/2        # force as even number
                    elif name=="size_in_kb":
                        Partition["size_in_kb"]=int(value)
                        if Partition["size_in_kb"]==1:
                            print "\nERROR: Invalid partition size of 1KB"
                            sys.exit()  # error
                        Partition["size_in_kb"]=2*(int(value)/2)    # force as even number
                    else:
                        Partition[name]=value

                if FileFound == 1:
                    Partition['filename'].append("")
                    Partition['fileoffset'].append(0)
                    Partition['filepartitionoffset'].append(0)
                    Partition['appsbin'].append("false")

                ## done with all the elements, now ensure that size matches with size_in_kb
                Partition["size"] = 2*Partition["size_in_kb"]

                ## Now add this "Partition" object to the PartitionCollection
                ## unless it's the label EXT, which is a left over legacy tag

                if Partition['label'] != 'EXT':
                    #print "\nJust added %s" % Partition['label']
                    PartitionCollection.append( Partition )

                    #print "Adding PartitionCollection to \"PhyPartition\" of size %i" % (NumPhyPartitions-1)
                    PhyPartition[(NumPhyPartitions-1)]          = PartitionCollection

                    #print "\nPartition stored (%i partitions total)" % len(PartitionCollection)

            else:
                print "ERROR: element.tag was partition, primary or extended, but it had no keys!"
                sys.exit()  # error

        elif element.tag=="file":
            #print "Found a file, NumPhyPartitions=",NumPhyPartitions    ## i.e. just a file tag (usually in legacy)
            #print PhyPartition[(NumPhyPartitions-1)]
            #print "Current partition is \"%s\"\n" % Partition['label']

            Partition['filename'].append("")
            Partition['fileoffset'].append(0)
            Partition['filepartitionoffset'].append(0)
            Partition['appsbin'].append("false")

            if element.keys():
                for name, value in element.items():
                    if name=='name' or name=='filename' :
                        Partition['filename'][-1] = value
                    if name=='fileoffset':
                        Partition['fileoffset'][-1] = value
                    if name=='offset' or name=='filepartitionoffset':
                        Partition['filepartitionoffset'][-1] = int(value)
                    if name=='appsbin':
                        Partition['appsbin'][-1] = value

                    #Partition[name]=value

            #print Partition['filename']

            #print "\n============================================="
            #for z in range(len(Partition['filename'])):
            #    print "Partition['filename'][",z,"]=",Partition['filename'][z]
            #    print "Partition['fileoffset'][",z,"]=",Partition['fileoffset'][z]
            #    print "Partition['filepartitionoffset'][",z,"]=",Partition['filepartitionoffset'][z]
            #    print "Partition['appsbin'][",z,"]=",Partition['appsbin'][z]
            #    print " "

            #print "Showing the changes to PartitionCollection"
            #print PartitionCollection[-1]


    if 'WRITE_PROTECT_BOUNDARY_IN_KB' in HashInstructions:
        if type(HashInstructions['WRITE_PROTECT_BOUNDARY_IN_KB']) is str:
            m = re.search("^(\d+)$", HashInstructions['WRITE_PROTECT_BOUNDARY_IN_KB'])
            if type(m) is NoneType:
                ## we didn't match, so assign deafult
                HashInstructions['WRITE_PROTECT_BOUNDARY_IN_KB'] = 0
            else:
                HashInstructions['WRITE_PROTECT_BOUNDARY_IN_KB'] = int(HashInstructions['WRITE_PROTECT_BOUNDARY_IN_KB'])
    else:
        #print "WRITE_PROTECT_BOUNDARY_IN_KB does not exist"
        HashInstructions['WRITE_PROTECT_BOUNDARY_IN_KB'] = 65536


    if 'GROW_LAST_PARTITION_TO_FILL_DISK' in HashInstructions:
        if type(HashInstructions['GROW_LAST_PARTITION_TO_FILL_DISK']) is str:
            m = re.search("^(true)$", HashInstructions['GROW_LAST_PARTITION_TO_FILL_DISK'] ,re.IGNORECASE)
            #print type(m)
            if type(m) is NoneType:
                HashInstructions['GROW_LAST_PARTITION_TO_FILL_DISK'] = False    # no match
                #print "assigned false"
            else:
                HashInstructions['GROW_LAST_PARTITION_TO_FILL_DISK'] = True     # matched string true
                #print "assigned true"
    else:
        HashInstructions['GROW_LAST_PARTITION_TO_FILL_DISK'] = False


    if 'DISK_SIGNATURE' in HashInstructions:
        if type(HashInstructions['DISK_SIGNATURE']) is str:
            m = re.search("^0x([\da-fA-F]+)$", HashInstructions['DISK_SIGNATURE'])
            if type(m) is NoneType:
                print "WARNING: DISK_SIGNATURE is not formed correctly, expected format is 0x12345678\n"
                HashInstructions['DISK_SIGNATURE'] = 0x00000000
            else:
                HashInstructions['DISK_SIGNATURE'] = int(HashInstructions['DISK_SIGNATURE'],16)
    else:
        print "DISK_SIGNATURE does not exist"
        HashInstructions['DISK_SIGNATURE'] = 0x00000000

    if 'ALIGN_BOUNDARY_IN_KB' in HashInstructions:
        if type(HashInstructions['ALIGN_BOUNDARY_IN_KB']) is str:
            m = re.search("^(\d+)$", HashInstructions['ALIGN_BOUNDARY_IN_KB'])
            if type(m) is NoneType:
                ## we didn't match, so assign deafult
                HashInstructions['ALIGN_BOUNDARY_IN_KB'] = HashInstructions['WRITE_PROTECT_BOUNDARY_IN_KB']
            else:
                HashInstructions['ALIGN_BOUNDARY_IN_KB'] = int(HashInstructions['ALIGN_BOUNDARY_IN_KB'])
    else:
        #print "ALIGN_BOUNDARY_IN_KB does not exist"
        HashInstructions['ALIGN_BOUNDARY_IN_KB'] = HashInstructions['WRITE_PROTECT_BOUNDARY_IN_KB']

    print "HashInstructions['WRITE_PROTECT_BOUNDARY_IN_KB']    =%d" % HashInstructions['WRITE_PROTECT_BOUNDARY_IN_KB']
    print "HashInstructions['ALIGN_BOUNDARY_IN_KB']            =%d" % HashInstructions['ALIGN_BOUNDARY_IN_KB']
    print "HashInstructions['GROW_LAST_PARTITION_TO_FILL_DISK']=%s" % HashInstructions['GROW_LAST_PARTITION_TO_FILL_DISK']
    print "HashInstructions['DISK_SIGNATURE']=0x%X" % HashInstructions['DISK_SIGNATURE']

    #for j in range(len(PhyPartition)):
    #for j in range(1):
    #    print "\n\nPhyPartition[%d] ========================================================= " % (j)
    #    PrintPartitionCollection( PhyPartition[j] )


    print "len(PhyPartition)=",len(PhyPartition)

    if HashInstructions['GROW_LAST_PARTITION_TO_FILL_DISK']==False:
        ## to be here means we're *not* growing final partition, thereore, obey the sizes they've specified
        for j in range(len(PhyPartition)):
            TempNumPartitions = len(PhyPartition[j])
            if TempNumPartitions>4:
                MinSectorsNeeded = 1 + (TempNumPartitions-3) # need MBR + TempNumPartitions-3 EBRs
            else:
                MinSectorsNeeded = 1    # need MBR only

            for Partition in PhyPartition[j]:
                print "LABEL: '%s' with %d sectors " % (Partition['label'],int(Partition["size_in_kb"]*2))

                MinSectorsNeeded += int(Partition["size_in_kb"]*2)

                #print "LABEL '%s' with size %d sectors" % (Partition['label'],Partition['size_in_kb']/2)


    print "MinSectorsNeeded=%d" % MinSectorsNeeded
    #sys.exit()

#    PrintPartitionCollection( PhyPartition[0] )
def PrintPartitionCollection(PartitionCollection):

    #print PartitionCollection

    for Partition in PartitionCollection:
        print Partition
        print " "
        for key in Partition:
            print key,"\t=>\t",Partition[key]

    #for j in range(NumMBRPartitions):





# A8h reflected is 15h, i.e. 10101000 <--> 00010101
def reflect(data,nBits):

    reflection = 0x00000000
    bit = 0

    for bit in range(nBits):
        if(data & 0x01):
            reflection |= (1 << ((nBits - 1) - bit))
        data = (data >> 1);

    return reflection


def CalcCRC32(array,len):
   k        = 8;            # length of unit (i.e. byte)
   MSB      = 0;
   gx       = 0x04C11DB7;   # IEEE 32bit polynomial
   regs     = 0xFFFFFFFF;   # init to all ones
   regsMask = 0xFFFFFFFF;   # ensure only 32 bit answer

   for i in range(len):
      DataByte = array[i]
      DataByte = reflect( DataByte, 8 );

      for j in range(k):
        MSB  = DataByte>>(k-1)  ## get MSB
        MSB &= 1                ## ensure just 1 bit

        regsMSB = (regs>>31) & 1

        regs = regs<<1          ## shift regs for CRC-CCITT

        if regsMSB ^ MSB:       ## MSB is a 1
            regs = regs ^ gx    ## XOR with generator poly

        regs = regs & regsMask; ## Mask off excess upper bits

        DataByte <<= 1          ## get to next bit


   regs          = regs & regsMask ## Mask off excess upper bits
   ReflectedRegs = reflect(regs,32) ^ 0xFFFFFFFF;

   return ReflectedRegs

def ReturnLow32bits(var):
    return var & 0xFFFFFFFF

def ReturnHigh32bits(var):
    return (var>>32) & 0xFFFFFFFF


def PrintBanner(sz):
    print "\n----------------" + sz + "---------------------"


def ShowUsage():
    print "\nUsage:\npython ParseGPT.py gpt.bin"


def CreateFinalPartitionBin():
    opfile = open("partition.bin", "wb")

    for i in range(3):
        FileName = "partition%i.bin" % i;
        size     = 0

        if os.path.isfile(FileName):
            size = os.path.getsize(FileName)

            ipfile = open(FileName, "rb")
            temp = ipfile.read()
            opfile.write(temp)
            ipfile.close()

        if size < 8192:
            MyArray = [0]*(8192-size)
            for b in MyArray:
                opfile.write(struct.pack("B", b))

    opfile.close()



def UpdatePartitionTable(Bootable,Type,StartSector,Size,Offset,Record):

    #print "Size = %i" % Size

    if Bootable=="true":
        Bootable = 0x80
    else:
        Bootable = 0x00

    # for type I must support the original "4C" and if they put "0x4C"
    m = re.search("^(0x)?([a-fA-F\d][a-fA-F\d]?)$", Type)
    if type(m) is NoneType:
        print "\tWARNING: Type \"%s\" is not in the form 0x4C, set to 0x00" % Type
        Type = 0x00
    else:
        #print m.group(2)
        #print "---------"
        Type = int(m.group(2),16)
        #print "\tType is \"0x%X\"" % Type

    #print "\tAt Offset=0x%.4X (%d) (%d bytes left)" % (Offset,Offset,len(Record)-Offset)

    Record[Offset]         = Bootable  ; Offset+=1

    Record[Offset:Offset+3]= [0,0,0]   ; Offset+=3

    Record[Offset]         = Type      ; Offset+=1

    Record[Offset:Offset+3]= [0,0,0]   ; Offset+=3

    # First StartSector
    for b in range(4):
        Record[Offset] = ((StartSector>>(b*8)) & 0xFF) ; Offset+=1

    # First StartSector
    for b in range(4):
        Record[Offset] = ((Size>>(b*8)) & 0xFF) ; Offset+=1

    #print "\t\tBoot:0x%.2X, ID:0x%.2X, 0x%.8X, 0x%.8X (%.2fMB)" % (Bootable,Type,StartSector,Size,Size/2048.0)

    return Record





def ParseCommandLine():
    global GPTFile,OutputToCreate,PhysicalPartitionNumber

    if len(sys.argv) > 2:
        ShowUsage()
        sys.exit()  # error

    print "\nInput GTP File = %s\n" % sys.argv[1]
    GPTFile = sys.argv[1];

    #Parse "gpt.bin" passed as command line argument
    if not os.path.exists(GPTFile):
        print "ERROR: '%s' not found\n" % GPTFile
        sys.exit()      # error
    else:
        print "GPT FILE: '%s' exists\n" % GPTFile


def ParseGPTHeader():
    global GPTHeader,PhyPartitionStartSector,PhyPartitionEndSector,NumPhyPartitions,CurrentLBA,BackupLBA

    print "\nParsing GPT Header..."
    if (GPTHeader[0:8] == [0x45,0x46,0x49,0x20,0x50,0x41,0x52,0x54]):             #"EFI PART"
        print "EFI PART Found!!!"

        #Physical Partition Start Sector
        for i in range(8) :
            PhyPartitionStartSector |= (GPTHeader[40+i]<<i*8)
        print "PhyPartitionStartSector = %d(0x%X)" % (PhyPartitionStartSector,PhyPartitionStartSector)

        #Physical Partition End Sector
        for i in range(8) :
            PhyPartitionEndSector |= (GPTHeader[48+i]<<i*8)
        print "PhyPartitionEndSector = %d(0x%X)" % (PhyPartitionEndSector,PhyPartitionEndSector)

        #Physical Partition Number
        for i in range(4) :
            NumPhyPartitions |= (GPTHeader[80+i]<<i*8)
        print "NumPhyPartitions = %d(0x%X)" % (NumPhyPartitions,NumPhyPartitions)

        #Current LBA
        for i in range(8) :
            CurrentLBA |= (GPTHeader[24+i]<<i*8)
        print "Current LBA = %d(0x%X)" % (CurrentLBA,CurrentLBA)

        #Backup LBA
        for i in range(8) :
            BackupLBA |= (GPTHeader[32+i]<<i*8)
        print "Backup LBA = %d(0x%X)" % (BackupLBA,BackupLBA)
    else:
        print "EFI PART Not Found!!!"



def ParseGPTContent():
    global GPTContent,NumPhyPartitions,PartitionCollection

    print "\nParsing GPT Content..."

    for i in range(NumPhyPartitions):
        PartitionCollection[i] = partition()

        for j in range(36) :
            PartitionCollection[i].label += chr(GPTContent[56+i*128+2*j]|(GPTContent[56+i*128+2*j+1]<<8)).rstrip('\0')
        if PartitionCollection[i].label == '':        #Correct Some Wrong Partition Number in GPT Header.
            NumPhyPartitions = i
            break
        print "\nPartition %d :" % (i+1)
        print "label = %s" % PartitionCollection[i].label

        for j in range(16) :
            PartitionCollection[i].typeGUID |= (GPTContent[i*128+j]<<j*8)
            PartitionCollection[i].GUID |= (GPTContent[16+i*128+j]<<j*8)
            PartitionCollection[i].SECTOR_SIZE_IN_BYTES = 512
            PartitionCollection[i].file_sector_offset = 0
            PartitionCollection[i].filename = ''
        print "Partition Type GUID = 0x%X" % PartitionCollection[i].typeGUID
        print "Partition GUID = 0x%X" % PartitionCollection[i].GUID

        for j in range(8) :
            PartitionCollection[i].start_sector |= (GPTContent[32+i*128+j]<<j*8)
            PartitionCollection[i].end_sector |= (GPTContent[40+i*128+j]<<j*8)
        print "start_sector = %d" % PartitionCollection[i].start_sector
        print "end_sector = %d" % PartitionCollection[i].end_sector

        for j in range(8) :
            PartitionCollection[i].attr |= (GPTContent[48+i*128+j]<<j*8)
        print "attr = 0x%X" % PartitionCollection[i].attr

        PartitionCollection[i].num_partition_sectors = PartitionCollection[i].end_sector - PartitionCollection[i].start_sector + 1
        PartitionCollection[i].size_in_KB = PartitionCollection[i].num_partition_sectors/2.0
        PartitionCollection[i].start_byte_hex = PartitionCollection[i].start_sector * PartitionCollection[i].SECTOR_SIZE_IN_BYTES

        print "num_partition_sectors = %d" % PartitionCollection[i].num_partition_sectors
        print "size_in_KB = %d" % PartitionCollection[i].size_in_KB
        print "start_byte_hex = 0x%X" % PartitionCollection[i].start_byte_hex

    print "\nThe disk has totally %d valid physical partitions" % NumPhyPartitions


def ParseGPT():
    global opfile,GPTFile,PrimaryGPT,BackupGPT,GPTHeader,GPTContent

    print "\nParsing GPT File..."
    print "The size of the GPT file %s is %d byte" % (GPTFile,os.path.getsize(GPTFile))

    opfile = open(GPTFile,'rb')
    tempfile = opfile.read()
    opfile.close()

    #convert string to int list
    for i in range(len(tempfile)):
        PrimaryGPT[i] = ord(tempfile[i])

    BackupGPT[0:32*512] = PrimaryGPT[2*512:34*512]
    BackupGPT[32*512:33*512] = PrimaryGPT[512:2*512]

    content_len = 32*512
    UpdatePrimaryGPT(0, 4, 512+88)  ## Zero Out Primary Content CRC.
    UpdatePrimaryGPT(0, 4, 512+16)  ## Zero Out Primary Header CRC.
    print "Content CRC = 0x%.8X len = %d" % (CalcCRC32(PrimaryGPT[2*512:],content_len), content_len)
    print "Header CRC = 0x%.8X len = 92" % CalcCRC32(PrimaryGPT[512:],92)


    if ((PrimaryGPT[510] == 0x55) and (PrimaryGPT[511] == 0xAA)):
        GPTHeader = PrimaryGPT[1*512:2*512]
        GPTContent = PrimaryGPT[2*512:34*512]
        #ParseGPTHeader()
        #ParseGPTContent()
    else:
        print "Error :Not a Valid GPT File"


def Prettify(element):
    #Return a pretty-printed XML string for the Element.
    rough_string = ET.tostring(element, 'utf-8')
    reparsed = minidom.parseString(rough_string)
    return reparsed.toprettyxml(indent="  ")


def CreateRawProgramXMLFile():
    global opfile,PartitionCollection,RawProgramXML

    print "\nMaking \"%s\"" % RAW_PROGRAM

    RawProgramXML = Element('data')
    RawProgramXML.append(Comment("NOTE: This is an ** Autogenerated file **"))
    RawProgramXML.append(Comment('NOTE: Sector size is 512bytes'))

    #GUID Partitioning Table
    SubElement(RawProgramXML, 'program', {'SECTOR_SIZE_IN_BYTES':str(512),
                                          'file_sector_offset':str(0),
                                          'filename':'',
                                          'label':"PrimaryGPT",
                                          'num_partition_sectors':str(34),
                                          'partofsingleimage':"true",
                                          'physical_partition_number':str(0),
                                          'readbackverify':"false",
                                          'size_in_KB':str(17.0),
                                          'sparse':"false",
                                          'start_byte_hex':str(hex(0)),
                                          'start_sector':str(0)})
    #Physical Partition
    for i in range(NumPhyPartitions):
        SubElement(RawProgramXML, 'program', {'SECTOR_SIZE_IN_BYTES':str(PartitionCollection[i].SECTOR_SIZE_IN_BYTES),
                                              'file_sector_offset':str(PartitionCollection[i].file_sector_offset),
                                              'filename':PartitionCollection[i].filename,
                                              'label':PartitionCollection[i].label,
                                              'num_partition_sectors':str(PartitionCollection[i].num_partition_sectors),
                                              'partofsingleimage':PartitionCollection[i].partofsingleimage,
                                              'physical_partition_number':str(PartitionCollection[i].physical_partition_number),
                                              'readbackverify':PartitionCollection[i].readbackverify,
                                              'size_in_KB':str(PartitionCollection[i].size_in_KB),
                                              'sparse':PartitionCollection[i].sparse,
                                              'start_byte_hex':hex(PartitionCollection[i].start_byte_hex).rstrip('L'),
                                              'start_sector':str(PartitionCollection[i].start_sector)})
    opfile = open(RAW_PROGRAM, "w")
    opfile.write( Prettify(RawProgramXML) )
    opfile.close()
    print "\"%s\" Created" % RAW_PROGRAM



def CreateGPTPartitionTable():
    global opfile,PrimaryGPT,BackupGPT,NUM_DISK_SECTORS

    print "\nMaking GUID Partitioning Table (GPT):"

    print NumPhyPartitions

    UpdatePrimaryGPT(0, 4, 512+16)  ## Zero Out Primary Header CRC.
    UpdatePrimaryGPT(1, 8, 512+24)  ## Update Primary Header with CurrentLBA.
    UpdatePrimaryGPT(NUM_DISK_SECTORS-1, 8, 512+32)  ## Update Primary Header with BackupLBA.
    UpdatePrimaryGPT(34, 8, 512+40)  ## Update Primary Header with FirstUseableLBA.
    UpdatePrimaryGPT(NUM_DISK_SECTORS-34, 8, 512+48)  ## Update Primary Header with LastUseableLBA.
    UpdatePrimaryGPT(2, 8, 512+72)  ## Update Primary Header with Partition Array Location.
    UpdatePrimaryGPT(NumPhyPartitions, 4, 512+80)  ## Update Primary Header with Actual Partition Number.
    UpdatePrimaryGPT(0, 4, 512+88)  ## Zero Out Primary Content CRC.
    UpdatePrimaryGPT(NUM_DISK_SECTORS-34, 8, 2*512+(NumPhyPartitions-1)*128+40)  ## Update last partition 'userdata' with actual size in Primary Header.
    ## !!!Note!!!    CRC MUST be calculted **After** all PrimaryGPT data was updated
    UpdatePrimaryGPT(CalcCRC32(PrimaryGPT[2*512:], 3072), 4, 512+88)  ## Update Primary Content CRC
    UpdatePrimaryGPT(CalcCRC32(PrimaryGPT[512:], 92), 4, 512+16)  ## Update Primary Header CRC

    UpdateBackupGPT(0, 4, 32*512+16)  ## Zero Out Backup Header CRC.
    UpdateBackupGPT(NUM_DISK_SECTORS-1, 8, 32*512+24)  #Update Backup Header with CurrentLBA.
    UpdateBackupGPT(1, 8, 32*512+32)  ## Update Backup Header with BackupLBA.
    UpdateBackupGPT(34, 8, 32*512+40)  ## Update Backup Header with FirstUseableLBA.
    UpdateBackupGPT(NUM_DISK_SECTORS-34, 8, 32*512+48)  ## Update Backup Header with LastUseableLBA.
    UpdateBackupGPT(NUM_DISK_SECTORS-33, 8, 32*512+72)  ## Update Backup Header with Partition Array Location.
    UpdateBackupGPT(NumPhyPartitions, 4, 32*512+80)  ## Update Backup Header with Actual Partition Number.
    UpdateBackupGPT(0, 4, 32*512+88)  ## Zero Out Backup Content CRC.
    UpdateBackupGPT(NUM_DISK_SECTORS-34, 8, (NumPhyPartitions-1)*128+40)  ## Update last partition 'userdata' with actual size in Backup Header.
    ## !!!Note!!!    CRC MUST be calculted **After** all BackupGPT data was updated
    UpdateBackupGPT(CalcCRC32(BackupGPT[0:], 3072), 4, 32*512+88)  ## Update Backup Content CRC
    UpdateBackupGPT(CalcCRC32(BackupGPT[32*512:], 92), 4,512+16)  ## Update Backup Header CRC

    ## Now we have all data of PrimaryGPT and BackupGPT,so we can write them to hard disk.
    WriteGPT(0)


## ==============================================================================================
## ==============================================================================================
## ==============================================================================================
## ======================================main()==================================================
## ==============================================================================================
## ==============================================================================================
## ==============================================================================================

GPTFile = "gpt.bin"                 ## sys.argv[1]
RAW_PROGRAM = 'rawprogram.xml'
PATCHES = 'patch.xml'


ParseCommandLine()
ParseGPT()                   ## automatically parses GPTFile
#CreateRawProgramXMLFile()
#CreateGPTPartitionTable()

