import hashlib # 보안 해시와 메세지 요약 알고리즘에 대한 공통 인터페이스.
import time
import csv # csv파일을 읽기 위해서 파이썬에 내장된 csv 모듈 import
import random
from http.server import BaseHTTPRequestHandler, HTTPServer
from socketserver import ThreadingMixIn ## 동기적으로 요청을 다루는 프레임워크.
import json
import re ## 정규표현식 라이브러리
from urllib.parse import parse_qs
from urllib.parse import urlparse
#urllib은 파이썬 표준 라이브러리 중 하나다. HTTP 요청, 파싱과 관련된 하위 패키지들이 존재하며,
# URL 파싱과 관련된 것들은 거의 다 urllib.parse에 들어 있다
import threading
import cgi # common gatewaya interface
import uuid # universial unique identifier
from tempfile import NamedTemporaryFile
# tempfile 임시 파일과 디렉토리를 만드는 모듈.
# NamedTemporaryFile은 자동 정리를 제공, 컨텍스트 관리자로 사용할 수 있는 고수준 인터페이스.
import shutil # 파일과 파일 모음에 대한 여러 가지 고수준 연산을 제공.
import requests # for sending new block to other nodes

# 20190605 /(YuRim Kim, HaeRi Kim, JongSun Park, BohKuk Suh , HyeongSeob Lee, JinWoo Song)
from multiprocessing import Process, Lock # for using Lock method(acquire(), release())
# multiprocessing 모듈을 이용해 스포닝(부모 프로세스가 운영체제에 요청하여 자식 프로세스를 새로 만들어내는 과정)
# 을 쉽게 수행할 수 있도록 한다. 보통 부모 프로세스가 처리할 작업이 많은 경우 자식 프로세스를 새로 만들어 일부 작업을 자식 프로세스에게 위임하여 처리한다.
# for Put Lock objects into variables(lock)
# lock을 acquire하면 해당 쓰레드만 공유 데이터에 접근할 수 있고, lock을 release 해야만
# 다른 쓰레드에서 공유 데이터에 접근할 수 있습니다
lock = Lock()

PORT_NUMBER = 8666
g_txFileName = "txData.csv" ## 전역변수로 변수 설정.
g_bcFileName = "blockchain.csv" ## 블록 파일.
g_nodelstFileName = "nodelst.csv"
g_receiveNewBlock = "/node/receiveNewBlock"  ## 보류 - 아마 외부에서 받는 데이터인듯..
g_difficulty = 5 ## 난이도
g_maximumTry = 100
g_nodeList = {'127.0.0.1':'8668'} # trusted server list, should be checked manually


class Block:
        ## 자바의 생성자와 같은 역할. 초기화 메소드(self는 객체 자신, 인덱스, 이전 해쉬, timestamp, data, 현재 해쉬, 작업횟수)
    def __init__(self, index, previousHash, timestamp, data, currentHash, proof ):
        self.index = index
        self.previousHash = previousHash
        self.timestamp = timestamp
        self.data = data
        self.currentHash = currentHash
        self.proof = proof

    def toJSON(self):
        return json.dumps(self, default=lambda o: o.__dict__, sort_keys=True, indent=4)

class txData:
        ## 자바의 생성자와 같으 역할.초기화메소드(객체 자신, commitYN, 누가, 얼마를, 누구한테, 고유번호)
    def __init__(self, commitYN, sender, amount, receiver, uuid):
        self.commitYN = commitYN #채굴에 포함되었는지 여부를 의미하는데 초기값은 미채굴이므로 0이다.
        self.sender = sender
        self.amount = amount
        self.receiver = receiver
        self.uuid =  uuid ## 고유값

def generateGenesisBlock(): ## 제네시스 블록 생성 함수. readBlockChain 함수 실행 시 블록이 없을 때 호출됨.
    print("generateGenesisBlock is called")
    timestamp = time.time() ## 제네시스 블록엔 시간.
    print("time.time() => %f \n" % timestamp)
    tempHash = calculateHash(0, '0', timestamp, "Genesis Block", 0) ##  calculateHash 함수 호출.
    print(tempHash)
    return Block(0, '0', timestamp, "Genesis Block",  tempHash,0) ## 등의 파라미터를 블록에 던져준다.

def calculateHash(index, previousHash, timestamp, data, proof): ## 파라미터로 인덱스,이전해쉬,timestamp, data, 작업증명횟수
    value = str(index) + str(previousHash) + str(timestamp) + str(data) + str(proof) ## 전체를 문자열로 합치고
    sha = hashlib.sha256(value.encode('utf-8'))## ut8로 해쉬
    return str(sha.hexdigest()) ## 해당 해쉬값 리턴.

def calculateHashForBlock(block): ## 블록을 해쉬하는 함수..
    return calculateHash(block.index, block.previousHash, block.timestamp, block.data, block.proof)

def getLatestBlock(blockchain): ## 최근 블록 호출하는 함수. 길이 -1 이 최근 블록.
    return blockchain[len(blockchain) - 1]

def generateNextBlock(blockchain, blockData, timestamp, proof): ##블록 생성 함수. (블록전체데이터, 블록정보, 시간, 작업증명)
    previousBlock = getLatestBlock(blockchain) ## 최근블록
    nextIndex = int(previousBlock.index) + 1 ## 추가될 블록의 번호(최근블록 + 1)
    nextTimestamp = timestamp ## 시간
    nextHash = calculateHash(nextIndex, previousBlock.currentHash, nextTimestamp, blockData, proof)
    # index, previousHash, timestamp, data, currentHash, proof
    return Block(nextIndex, previousBlock.currentHash, nextTimestamp, blockData, nextHash, proof) ## 다음 블록생성.


# 20190605 / (YuRim Kim, HaeRi Kim, JongSun Park, BohKuk Suh , HyeongSeob Lee, JinWoo Song)
# /* WriteBlockchain function Update */
# If the 'blockchain.csv' file is already open, make it inaccessible via lock.acquire()
# After executing the desired operation, changed to release the lock.(lock.release())
# Reason for time.sleep ():
# prevents server overload due to repeated error message output and gives 3 seconds of delay to allow time for other users to wait without opening file while editing and saving csv file.
def writeBlockchain(blockchain): ## 블록체인에 블록 넣기.

    blockchainList = []

    for block in blockchain:
                    ## 인덱스와, 전 해쉬값, 시간, 블록데이터, 현재해쉬, 작업증명 의 6개 파라미터.
        blockList = [block.index, block.previousHash, str(block.timestamp), block.data, block.currentHash,block.proof ]
        blockchainList.append(blockList)

    #[STARAT] check current db(csv) if broadcasted block data has already been updated
    try:
        with open(g_bcFileName, 'r',  newline='') as file: ## blockchain.csv파일 읽기 모드로 읽어오기
            blockReader = csv.reader(file)
            last_line_number = row_count(g_bcFileName) ## 몇개의 블록이 있는지 확인. lastlineNumber = 블록의 마지막 인덱스+1
            for line in blockReader:
                if blockReader.line_num == last_line_number: ##line_num 메소드..iterable(반복가능한 객체)
                    ## iterator 객체 - 값을 차례대로 꺼낼 수 있는 객체.. line_num -> ctrl+b로 확인
                    ## 에일리어스 기반..(가명)
                    lastBlock = Block(line[0], line[1], line[2], line[3], line[4], line[5])

        ## 아직 배우지 않은 부분. 외부에서 받은 블록을 자기자신과 비교할때 해당 로직이 수행된다.
        if int(lastBlock.index) + 1 != int(blockchainList[-1][0]):
            print("index sequence mismatch")
            if int(lastBlock.index) == int(blockchainList[-1][0]):
                print("db(csv) has already been updated")
            return
    except:
        print("file open error in check current db(csv) \n or maybe there's some other reason")
        pass
        #return
    # [END] check current db(csv)
    openFile = False
    while not openFile: ## true면 반복문 탈출
        if blockchainList != []: ## 블록이 존재할 때
            try:
                lock.acquire() ## realse 전까지 lcok
                with open(g_bcFileName, "w", newline='') as file: ## 쓰기 모드로 연다.
                    writer = csv.writer(file) ## csv 파일 읽어오고.
                    writer.writerows(blockchainList) ## writerows -> 여러 라인 한번에 작성.
                    blockchainList.clear() ## 리스트 안 모든 요소 삭제. rowList, columnsList.
                    print("write ok")
                    openFile = True
                    for block in blockchain:
                        updateTx(block)
                    print('Blockchain written to blockchain.csv.')
                    print('Broadcasting new block to other nodes')
                    broadcastNewBlock(blockchain) ## 새 블록이 채굴됐을때 다른 노드에 알리는 함수 호출.
                    lock.release()
            except:
                    time.sleep(3)
                    print("writeBlockchain file open error")
                    lock.release()
        else:
            print("Blockchain is empty")

def readBlockchain(blockchainFilePath, mode = 'internal'): ## blockchain.csv 파일 읽어오기, 내부호출.
    print("readBlockchain")
    importedBlockchain = [] ## 추가된 블록을 넣을 배열.

    try:
        with open(blockchainFilePath, 'r',  newline='') as file:
            blockReader = csv.reader(file)
            for line in blockReader:
                block = Block(line[0], line[1], line[2], line[3], line[4], line[5])
                importedBlockchain.append(block) ## 파일의 전체 내용 리턴.

        print("Pulling blockchain from csv...")

        return importedBlockchain

    except: ## 오픈할 파일이 없는 경우. 예외로 빠진다.
        if mode == 'internal' : ## 내부에서 호출.
            blockchain = generateGenesisBlock() ## 제네시스 블록 생성
            importedBlockchain.append(blockchain) ## 빈 배열에 블록체인(제네시스 블록) append
            writeBlockchain(importedBlockchain) ## importedBlockchain(제네시스블록)을 블록체인에 넣는다.
            return importedBlockchain ## genesisblock return;
        else :
            return None

def updateTx(blockData) : ##Tx파일 updeate함수.
    ## 정규표현식.. \w - > 문자+숫자(alphanumeric)와 매치, [a-zA-Z0-9_]와 동일한 표현식이다.
    ## 정구표현식으로 컴파일.
    phrase = re.compile(r"\w+[-]\w+[-]\w+[-]\w+[-]\w+") # [6b3b3c1e-858d-4e3b-b012-8faac98b49a8]UserID hwang sent 333 bitTokens to UserID kim.
    matchList = phrase.findall(blockData.data) ## 해당 블록의 데이터를 컴파일 정규표현식으로 compile 후 phrase에 담고,
                                               ## 파라미터로 들어온 블록의 데이터와 비교.

    if len(matchList) == 0 : ## 일치하는 데이터가 없는 경우.
        print ("No Match Found! " + str(blockData.data) + "block idx: " + str(blockData.index))
        return

    tempfile = NamedTemporaryFile(mode='w', newline='', delete=False) ## 임시로 파일 생성.

    with open(g_txFileName, 'r') as csvfile, tempfile: ## 똑같은 파일을 두개의 변수에 담는다.
        reader = csv.reader(csvfile)
        writer = csv.writer(tempfile)
        for row in reader: ## 열이 아닌 행 반복.
            if row[4] in matchList: ## row4?? ## 정규표현식이 있는 경우
                print('updating row : ', row[4]) ## 정규표현식 프린트
                row[0] = 1 ## 인덱스 = 1로 바꾼다.. 왜? 아.. 업데이트 된 블록의 인덱스는 1로 바뀌니까!
            writer.writerow(row) ## 바꾸고 writer파일에 없데이트. 인덱스가 1로 바뀌었겠지?

    shutil.move(tempfile.name, g_txFileName) ## shitil = 연산 모듈. 업데이트한 tempfile을 txData.csv로 바꾼다.
    csvfile.close()
    tempfile.close()
    print('txData updated')

# 20190605 /(YuRim Kim, HaeRi Kim, JongSun Park, BohKuk Suh , HyeongSeob Lee, JinWoo Song)
# /* writeTx function Update */
# If the 'txData.csv' file is already open, make it inaccessible via lock.acquire()
# After executing the desired operation, changed to release the lock.(lock.release())
# Reason for time.sleep ():
# prevents server overload due to repeated error message output and gives 3 seconds of delay to allow time for other users to wait without opening file while editing and saving csv file.
# Removed temp files to reduce memory usage and increase work efficiency.
def writeTx(txRawData): ## txRawData == newTxData
    print(g_txFileName)
    txDataList = [] ## 새로운 데이터에 대한 임시 리스트
    txOriginalList = []
    for txDatum in txRawData: ## for txDatum in txRawData: 데이터의 길이만큼 반복문 돌기.
        txList = [txDatum.commitYN, txDatum.sender, txDatum.amount, txDatum.receiver, txDatum.uuid] ## commitYN은 1,0이구나.
        ## 새로운 tx에 대한 내용을 빈 배열 txLIst에 추가하고
        txDataList.append(txList) ## 그걸 또 빈 배열 txDataList에 추가한다. 현재는 추가된 내용이 txDataList에 있겠지.

    try:
        with open(g_txFileName, 'r', newline='') as csvfile: ##  그 후에, txData.csv 읽어오기.
            reader = csv.reader(csvfile)
            for row in reader: ## 원래 있던 row내용만큼 반복문 돌아서
                txOriginalList.append(row) ## txOriginalList에 원래 txData파일의 내용을 append 한다. 위의 txDAtaList 와는 별개.

            openWriteTx = False
            while not openWriteTx: ## openWriteTx가 true일 때 break;
                lock.acquire() ## 한 프로세스 내 쓰레드들은 (가상) 메모리 내 힙, 스택, 코드 영역을 공유한다.
                               ##파이썬의 GIL과는 별개로, 쓰레드간 공유되는 데이터의 경쟁은 데이터를 꼬이게 만들 수 있다.
                               ##python threading 패키지에서는 Lock을 지원한다.
                               ##lock을 acquire하면 해당 쓰레드만 공유 데이터에 접근할 수 있고, lock을 release 해야 다른 쓰레드에서 공유 데이터에 접근할 수 있다.
                               ##Lock을 사용. 특정 쓰레드가 작업을 마치기 전 까지 다른 쓰레드가 Shared Data에 접근할 수 없도록 함

                try:
                    print("NewTxData lock.acquire")
                    with open(g_txFileName, 'w', newline='') as csvfile: ##  txData.csv 읽어오고
                        writer = csv.writer(csvfile) ## writer 변수에 넣고
                        # adding new tx
                        writer.writerows(txOriginalList) ## 원래 내용 추가하고.
                        writer.writerows(txDataList) ## 새 내용 추가하고.
                        print("writeTx write ok")
                        csvfile.close() ## 종료하는데, 이러면 원래 데이터가 계속 더해지는게 아닌가?
                                        ## 파일 이름을 새로 덮어쓰니까, 중복되진 않는다.(교수님 왈)
                        openWriteTx = True
                        lock.release()

                except Exception as e:
                    print(e)
                    time.sleep(3)
                    print("file open error") ## 에러.
                    lock.release()
    except:
        # this is 1st time of creating txFile
        try:
            with open(g_txFileName, "w", newline='') as file:
                writer = csv.writer(file)
                writer.writerows(txDataList)
        except:
            return 0
    return 1
    print('txData written to txData.csv.')

def readTx(txFilePath): ## 경로에 해당되는 파일을 읽어오는 함수.
    print("readTx")
    importedTx = []  ## 추가된 tx파일을 넣을 빈 배열 선언하고.

    try:
        with open(txFilePath, 'r',  newline='') as file: ## txData.csv 읽어오기 read 모드로.
            txReader = csv.reader(file) ## txReader라는 변수에 넣고,
            for row in txReader: ## 각각의 행 데이터를 수집하기 위해 반복문.
                if row[0] == '0': # find unmined txData. row[0]이라는 거는 아직 거래가 확정되지 않은 txData라는거.
                    line = txData(row[0],row[1],row[2],row[3],row[4])
                    importedTx.append(line) # 그럴 경우에 importedTx에 추가.
        print("Pulling txData from csv...")
        return importedTx ## 추가된 내용을 리턴.
    except:
        return []

def getTxData(): ##txData 읽어오기.
    strTxData = ''
    importedTx = readTx(g_txFileName) ## txdata.csv를 읽어서 ImportedTx로. 추가된 내용이 importedTx로 return된다.
    if len(importedTx) > 0 : ## 0보다 큰 경우 즉 거래 내용이 있는 경우.
        for i in importedTx: ## 해당 길이만큼 반복문.
            print(i.__dict__) ## i.__dict__ 어떤 클래스의 객체에 데해서 키와 밸류 형식으로 리턴해주는 내장 함수
            ## 거래 내용
            transaction = "["+ i.uuid + "]" "UserID " + i.sender + " sent " + i.amount + " bitTokens to UserID " + i.receiver + ". " #
            print(transaction) ## 거래내용 출력
            strTxData += transaction ## strTxData에 거래내용 넣기(배열로)

    return strTxData ## 원래 있던 내용과 추가된 내용을 넣어 리턴.

def mineNewBlock(difficulty=g_difficulty, blockchainPath=g_bcFileName): ## 전역 변수로 설정된 난이도와, 파일이름.
    blockchain = readBlockchain(blockchainPath) ## blockchainPath는 파일이름, 배열로 받아 blockchain 변수에 담는다.
    strTxData = getTxData() ## getTxTata txData배열 리턴받음.
    if strTxData == '' : ## 빈 내용일 때! 즉 txData에 거래 내역이 없을 때.
        print('No TxData Found. Mining aborted') ## 채굴할 필요가 없다.
        return ## 함수 종료

    ## txData에 거래 내용이 있는 경우에
    timestamp = time.time()
    proof = 0
    newBlockFound = False

    print('Mining a block...')
    ## 밑에는 채굴 반복문.
    while not newBlockFound: ## 원래 값이 false니까.. true로 바뀔 때 까지 즉 새로운 블록이 생성될 때 까지 반복문.
        newBlockAttempt = generateNextBlock(blockchain, strTxData, timestamp, proof)
        if newBlockAttempt.currentHash[0:difficulty] == '0' * difficulty: ## 난이도에 맞을때. proof랑, timestamp가 바뀔듯.
            stopTime = time.time()
            timer = stopTime - timestamp
            print('New block found with proof', proof, 'in', round(timer, 2), 'seconds.')
            newBlockFound = True ## 채굴 완료시 True.
        else:
            proof += 1

    blockchain.append(newBlockAttempt) ## 해당 블록의 데이터 blockchain 변수에 데이터 넣고 .
    writeBlockchain(blockchain) ## 블록 생성.

def mine(): ## 채굴 함수 실행.
    mineNewBlock()

def isSameBlock(block1, block2): ## 파라미터로 받은 두 블록이 같은지 확인하는 함수. true or false 리턴.
    if str(block1.index) != str(block2.index):
        return False
    elif str(block1.previousHash) != str(block2.previousHash):
        return False
    elif str(block1.timestamp) != str(block2.timestamp):
        return False
    elif str(block1.data) != str(block2.data):
        return False
    elif str(block1.currentHash) != str(block2.currentHash):
        return False
    elif str(block1.proof) != str(block2.proof):
        return False
    return True

def isValidNewBlock(newBlock, previousBlock): ## 새 블록과 이전블록의 데이터를 비교, 타당한 블록인지 확인하는 함수. true or false.
    if int(previousBlock.index) + 1 != int(newBlock.index):
        print('Indices Do Not Match Up')
        return False
    elif previousBlock.currentHash != newBlock.previousHash:
        print("Previous hash does not match")
        return False
    elif calculateHashForBlock(newBlock) != newBlock.currentHash:
        print("Hash is invalid")
        return False
    elif newBlock.currentHash[0:g_difficulty] != '0' * g_difficulty:
        print("Hash difficulty is invalid")
        return False
    return True

def newtx(txToMining): ## tempdict(key:value)를 파라미터로 받는다.

    newtxData = [] ## 새로운 값을 넣을 배열 선언.
    # transform given data to txData object
    for line in txToMining: ## body에서 받은 tempDict 반복문으로 수집
        tx = txData(0, line['sender'], line['amount'], line['receiver'], uuid.uuid4())
        newtxData.append(tx) ## 수집한 데이터 newtxData에 append.

    # limitation check : max 5 tx
    if len(newtxData) > 5 : ## 5개가 넘는 초과된 거래내용이 요청됐을 때
        print('number of requested tx exceeds limitation')
        return -1 ## -1 리턴

    if writeTx(newtxData) == 0: ## 새로 추가될 거래내용이 없을 때..
        print("file write error on txData")
        return -2 ## return -2
    return 1 ## 정상적일 땐 1 리턴

def isValidChain(bcToValidate): ## 다른 블록체인을 파라미터로 받는다. 제네시스 블록의 여부를 통해 올바른 체인인가 판단하는 함수.
    genesisBlock = []
    bcToValidateForBlock = []

    # Read GenesisBlock
    try:
        with open(g_bcFileName, 'r',  newline='') as file: ## blockchain.csv 읽어와서
            blockReader = csv.reader(file) ## blockReader 변수에 넣고
            for line in blockReader:
                block = Block(line[0], line[1], line[2], line[3], line[4], line[5])
                genesisBlock.append(block) ## 데이터 수집 후 빈 배열에 append
#                break
    except:
        print("file open error in isValidChain") ## 파일 오픈 자체가 안되면 return False.
        return False

    # transform given data to Block object
    for line in bcToValidate: ## 입력받은 tempdict(key:value) 반복문 통해서 데이터 수집. 아마도 블록체인 자체가 들어오는듯.
        # print(type(line))
        # index, previousHash, timestamp, data, currentHash, proof
        block = Block(line['index'], line['previousHash'], line['timestamp'], line['data'], line['currentHash'], line['proof'])
        bcToValidateForBlock.append(block) ## 데이터 수집 후 빈 배열에 append

    #if it fails to read block data  from db(csv)
    if not genesisBlock: ## if문이 헷갈릴 수 있는데, 실험해보니 genesisBlock 배열이 비어있으면 if문에 해당.
        print("fail to read genesisBlock")
        return False

    # compare the given data with genesisBlock
    if not isSameBlock(bcToValidateForBlock[0], genesisBlock[0]): ## 서로의 인덱스가 0으로 같다. 즉 제네시스 블록이 서로 존재한다는것.
        print('Genesis Block Incorrect')
        return False

    # tempBlocks = [bcToValidateForBlock[0]]
    # for i in range(1, len(bcToValidateForBlock)):
    #    if isValidNewBlock(bcToValidateForBlock[i], tempBlocks[i - 1]):
    #        tempBlocks.append(bcToValidateForBlock[i])
    #    else:
    #        return False

    for i in range(0, len(bcToValidateForBlock)): ## 서로의 블록체인을 비교.
        if isSameBlock(genesisBlock[i], bcToValidateForBlock[i]) == False:
            return False

    return True

# 20190605 / (YuRim Kim, HaeRi Kim, JongSun Park, BohKuk Suh , HyeongSeob Lee, JinWoo Song)
# /* addNode function Update */
# If the 'nodeList.csv' file is already open, make it inaccessible via lock.acquire()
# After executing the desired operation, changed to release the lock.(lock.release())
# Reason for time.sleep ():
# prevents server overload due to repeated error message output and gives 3 seconds of delay to allow time for other users to wait without opening file while editing and saving csv file.
# Removed temp files to reduce memory usage and increase work efficiency.

## 위 내용 요약 -> nodeList.csv파일이 열려있는 경우 lock 건다, 그러고 작업 수행 후 release.
## time.sleep으로 딜레이를 준 이유는 서버 과부하를 막기 위함이다. 일의 효율성과 메모리 낭비를 줄이기 위해 temp files는 삭제했다.
def addNode(queryStr): # ex) {127.0.0.1:8668} 가 파라미터로(ip,port)
    # save
    previousList = []
    nodeList = []
    ## nodeList 배열에 ip,port 추가.
    nodeList.append([queryStr[0],queryStr[1],0]) # ip, port, # of connection fail

    try:
        with open(g_nodelstFileName, 'r', newline='') as csvfile: #  "nodelst.csv" 읽어오기. 현재 없는 상태.
            reader = csv.reader(csvfile) ## reader 변수에 넣고.
            for row in reader: ## 반복문 수행으로 데이터 수집.
                if row:
                    if row[0] == queryStr[0] and row[1] == queryStr[1]: ## 이미 ip와 port번호가 등록되어 있는 경우.
                        print("requested node is already exists")
                        csvfile.close()
                        nodeList.clear()
                        return -1
                    else:
                        previousList.append(row) ## 새로운 ip와 port인 경우는 append.

            openFile3 = False
            while not openFile3: ## true인 경우 반복문 탈출.
                lock.acquire() ## reales 전까지 lock.
                try:
                    with open(g_nodelstFileName, 'w', newline='') as csvfile: # "nodelst.csv" 읽어오기. 쓰기 모드.
                        writer = csv.writer(csvfile)  ## 원래 파일의 이름으로 새로 작성.(덮어쓰기 개념)
                        writer.writerows(nodeList) ## 데이터 넣고
                        writer.writerows(previousList) ## 새로운 데이터도 넣는다. 후에 종료.
                        csvfile.close()
                        nodeList.clear()
                        lock.release()
                        print('new node written to nodelist.csv.')
                        return 1
                except Exception as ex: ##에러인 경우. 언제 해당되는지는 잘 모르겠다. 아마도 경로나 이름?
                    print(ex)
                    time.sleep(3)
                    print("file open error")
                    lock.release()

    except:
        # this is 1st time of creating node list. nodelist를 처음 생성 할 때.
        try:
            with open(g_nodelstFileName, "w", newline='') as file: ## nodelist.csv 파일을 편집모드로 여는데, 처음엔 없으니 생성한다
                writer = csv.writer(file)
                writer.writerows(nodeList) ## ip,port 추가.
                nodeList.clear() ## 추가한 후에 nodeList는 비운다. columnList 비우는 거랑 같은 개념.
                print('new node written to nodelist.csv.')
                return 1
        except Exception as ex:
            print(ex)
            return 0

def readNodes(filePath): ## 노드 읽어오는 함수. 노드 추가할때 사용.
    print("read Nodes")
    importedNodes = []

    try:
        with open(filePath, 'r',  newline='') as file:
            txReader = csv.reader(file)
            for row in txReader:
                line = [row[0],row[1]] ## ip랑 port 인듯.
                importedNodes.append(line)
        print("Pulling txData from csv...")
        return importedNodes ## 추가된 노드 return.
    except:
        return []

def broadcastNewBlock(blockchain): ## 새 블록이 채굴됐을때 다른 노드에 알리는 함수. 탈중앙화니까.
    #newBlock  = getLatestBlock(blockchain) # get the latest block
    importedNodes = readNodes(g_nodelstFileName) # get server node ip and port. 파일로 읽어온다.(ip,port 적혀있는 csv파일 읽어오는듯)
    reqHeader = {'Content-Type': 'application/json; charset=utf-8'} ## 헤더의 내용.
    reqBody = [] ## body배열 선언. 아마도 새로 추가된 블록의 정보를 담을듯 하다.
    for i in blockchain:
        reqBody.append(i.__dict__) ## 바디에 업데이트된 블록 전체를 key:value 형태로 담는다.

    if len(importedNodes) > 0 :  ## 다른 노드가 있는 경우. 그쪽으로 리스폰을 보낸다.
        for node in importedNodes:
            try:
                URL = "http://" + node[0] + ":" + node[1] + g_receiveNewBlock  # http://ip:port/node/receiveNewBlock
                res = requests.post(URL, headers=reqHeader, data=json.dumps(reqBody))
                if res.status_code == 200: ## 정상 신호
                    print(URL + " sent ok.")
                    print("Response Message " + res.text)
                else:
                    print(URL + " responding error " + res.status_code)
            except:  ## 200이 안떴을때. 즉 "nodelst.csv" 있는 ip,port에 문제가 있는 경우.
                print(URL + " is not responding.")
                # write responding results
                tempfile = NamedTemporaryFile(mode='w', newline='', delete=False) ## Create and return a temporary file. 임시 파일 생성.
                try:
                    with open(g_nodelstFileName, 'r', newline='') as csvfile, tempfile: #"nodelst.csv" 읽어오기.
                        reader = csv.reader(csvfile) # 지정된 csvfile의 줄을 이터레이트 하는 판독기(reader) 객체를 반환 __next__() 메서드가 호출될 때마다 문자열을 반환하는 객체.
                        ## reader는 줄을 읽어오고
                        writer = csv.writer(tempfile) #지정된 파일류 객체에 분리된 문자열로 사용자의 데이터를 변환하는 기록기(writer) 객체를 반환.
                        ## writer는 문자열을 하나씩 읽어온다.
                        for row in reader:
                            if row:
                                if row[0] == node[0] and row[1] ==node[1]: ##  서로 ip,port가 같을 때..? 둘다 같은 파일을 읽어왔는데 당연히 같지 않나?
                                    ## 인접노드 정보를 읽어와 브로드캐스팅시도를 하는데 해당노드가 수신불가 상태면 송신 실패가 될테고 그 실패횟수가 특정 기준치를 넘어서면 노드정보를 파일에서 지우는 동작.
                                    print("connection failed "+row[0]+":"+row[1]+", number of fail "+row[2]) ## row[2]는 뭐지. 실패한 횟수?
                                    tmp = row[2] ## 연결 실패횟수 tmp 변수에 담고.
                                    # too much fail, delete node.
                                    if int(tmp) > g_maximumTry:  ## > 100번 초과 실패시.
                                        print(row[0]+":"+row[1]+" deleted from node list because of exceeding the request limit")
                                    else:
                                        row[2] = int(tmp) + 1 ## 100번 안에
                                        # writer.writerow(row)
                                else:
                                    writer.writerow(row)
                    shutil.move(tempfile.name, g_nodelstFileName) ## 만들어진 tempfile에 갱신된 노드정보 파일을 덮어쓴다.
                    csvfile.close()
                    tempfile.close()
                except:
                    print("caught exception while updating node list")

def row_count(filename): ## 파일이
    try:
        with open(filename) as in_file:
            return sum(1 for _ in in_file) ## 변수값을 주지 않는다고 생각. 줄 횟수 전체를 읽어오는 공식. sum(1 for _ in in_file)
        ## 파이썬에서 언더스코어(_)는 다음과 같은 상황에서 사용되는데 크게 5가지의 경우가 있다.
        # 인터프리터(Interpreter)에서 마지막 값을 저장할 때
        # 값을 무시하고 싶을 때 (흔히 “I don’t care"라고 부른다.)
        # 변수나 함수명에 특별한 의미 또는 기능을 부여하고자 할 때
        # 국제화(Internationalization, i18n)/지역화(Localization, l10n) 함수로써 사용할 때
        # 숫자 리터럴값의 자릿수 구분을 위한 구분자로써 사용할 때
    except:
        return 0

def compareMerge(bcDict): ## 새 블록 받아서 비교 후 병합하는 함수. bcDict 는 body에 실려온 새 블록이다.

    heldBlock = [] ## 원래 있던 블록체인 배열
    bcToValidateForBlock = [] ## body에서 실려온(추가된) 체인 배열.

    # Read GenesisBlock
    try:
        with open(g_bcFileName, 'r',  newline='') as file: ## blockchain.csv 읽어오고
            blockReader = csv.reader(file) ## 줄 읽어와서 리스트로.
            #last_line_number = row_count(g_bcFileName)
            for line in blockReader:
                block = Block(line[0], line[1], line[2], line[3], line[4], line[5]) ## 개별 row의 데이터(블록) 수집
                heldBlock.append(block) ## 빈 heldBlock 배열에 blockchain.csv 정보 추가.
                #if blockReader.line_num == 1: 제네시스 블록만 있을 때
                #    block = Block(line[0], line[1], line[2], line[3], line[4], line[5])
                #    heldBlock.append(block)
                #elif blockReader.line_num == last_line_number:
                #    block = Block(line[0], line[1], line[2], line[3], line[4], line[5])
                #    heldBlock.append(block)

    except: ## 파일을 읽어오지 못할때.
        print("file open error in compareMerge or No database exists")
        print("call initSvr if this server has just installed")
        return -1

    #if it fails to read block data from db(csv)
    if len(heldBlock) == 0 : ## 블록데이터가 없을 때
        print("fail to read")
        return -2

    # transform given data to Block object
    for line in bcDict: ## 새 블록 내용 확인.
        # print(type(line))
        # index, previousHash, timestamp, data, currentHash, proof
        block = Block(line['index'], line['previousHash'], line['timestamp'], line['data'], line['currentHash'], line['proof'])
        bcToValidateForBlock.append(block) ## 빈 배열에 append

    # compare the given data with genesisBlock
    if not isSameBlock(bcToValidateForBlock[0], heldBlock[0]): ## 서로의 제네시스 블록이 같지 않다면
        print('Genesis Block Incorrect')
        return -1

    # check if broadcasted new block,1 ahead than > last held block.. 하나의 블록이 추가됐을때만 사용 가능
    ## 한개 추가됐을 때만 확인할 수 있다는 뜻인듯.
    ## 밑에서 isValidNewBlock는 파라미터로 현재 블록과, 이전 블록을 받아 서로의 해쉬값을 비교하는 함수인데, 두개 이상의 데이터가 들어온다면 밑의 if문은 무조권 false가 된다.
    if isValidNewBlock(bcToValidateForBlock[-1],heldBlock[-1]) == False: ## 추가된 블록체인의 마지막 블록과 현재 체인의 마지막 블록을 비교. true 라면 heldBlock에 bcToValidateForBlock을 추가하는듯.

        # latest block == broadcasted last block 최근블록이 전송된 마지막 블록과 같을 때.
        if isSameBlock(heldBlock[-1], bcToValidateForBlock[-1]) == True: ## 서로의 마지막 블록이 같다면, 추가된게 없으니 이미 업데이트 된것.
            print('latest block == broadcasted last block, already updated')
            return 2
        # select longest chain
        elif len(bcToValidateForBlock) > len(heldBlock): ## 길이가 더 길때, 추가된 블록데이터가 있다.
            # validation. 타당성 검증
            if isSameBlock(heldBlock[0],bcToValidateForBlock[0]) == False: ## 서로의 제네시스 블록이 같지 않으면 타당x
                    print("Block Information Incorrect #1")
                    return -1
            tempBlocks = [bcToValidateForBlock[0]] ## 서로의 제네시스 블록이 같다면.
            for i in range(1, len(bcToValidateForBlock)): ## 추가된 데이터를 뽑기 위해 반복문.
                if isValidNewBlock(bcToValidateForBlock[i], tempBlocks[i - 1]): ## i-1즉, 하나의 블록데이터만 추가되었을 때를 가정했으니.. 현재블록,이전블록 비교했을 true면 append.
                    tempBlocks.append(bcToValidateForBlock[i]) ## tempbBlocks에 원래 데이터와 추가된 블록데이터 합혀서 추가. 1부터 시작했으니 제네시스 블록 제외(어차피 처음에 들어가있음)
                else:
                    return -1
            # [START] save it to csv
            # 20190605 / (kyuin Park, jiweon Lim, sunghoon Oh, sol Han )
            # TODO: append 정상여부 검증 필요
            blockchainList = []
            lengthGap = len(bcToValidateForBlock) - len(heldBlock)  # 받은 블록과 내 블록의 길이 차이. 1이겠지 뭐
            for block in bcToValidateForBlock[-lengthGap:]: ## 뒤에서부터 받아온다. 추가된 데이터만 받는다.
                blockList = [block.index, block.previousHash, str(block.timestamp), block.data,
                             block.currentHash, block.proof]
                blockchainList.append(blockList)  # blockchainList에 타노드의 block을 list 형태로 담아줌
            with open(g_bcFileName, "a", newline='') as file:
                writer = csv.writer(file)
                writer.writerows(blockchainList) ## csv파일 업데이트.

            # [END] save it to csv
            return 1
        elif len(bcToValidateForBlock) < len(heldBlock): ## 현재 노드의 blockChain의 크기가 더 클 때.
            # validation
            #for i in range(0,len(bcToValidateForBlock)):
            #    if isSameBlock(heldBlock[i], bcToValidateForBlock[i]) == False:
            #        print("Block Information Incorrect #1")
            #        return -1
            tempBlocks = [bcToValidateForBlock[0]] ## 타노드 체인의 제네시스블록.
            for i in range(1, len(bcToValidateForBlock)): ## 제네시스 블록 제외하고 반복문
                if isValidNewBlock(bcToValidateForBlock[i], tempBlocks[i - 1]): ## 현재블록과 이전블록의 해쉬값 비교하는 함수. true 면 append
                   tempBlocks.append(bcToValidateForBlock[i])
                else:
                    return -1
            print("We have a longer chain") ## 더 긴 체인을 가지고 있다.
            return 3
        else:
            print("Block Information Incorrect #2")
            return -1
    else: # very normal case (ex> we have index 100 and receive index 101 ...) ## 하나 추가된 데이터 = normal case. 일반적 경우
        tempBlocks = [bcToValidateForBlock[0]] ## 제네시스 블록 담고
        for i in range(1, len(bcToValidateForBlock)):
            if isValidNewBlock(bcToValidateForBlock[i], tempBlocks[i - 1]): ## 하나 차이나니까 isValidNewBlock 실행. true면 append.
                tempBlocks.append(bcToValidateForBlock[i])
            else:
                print("Block Information Incorrect #2 "+tempBlocks.__dict__) ## 데이터가 다를때, 해당 블록 정보 프린트
                return -1

        print("new block good") ## 새블록좋아(정상)

        # validation
        for i in range(0, len(heldBlock)): ## 서로의 블록을 다 비교(원래 있던 데이터만큼만)
            if isSameBlock(heldBlock[i], bcToValidateForBlock[i]) == False: ## 서로 다를 때.
                print("Block Information Incorrect #1")
                return -1
        # [START] save it to csv
        blockchainList = []
        for block in bcToValidateForBlock: ## 추가된 블록이 담긴 체인.
            blockList = [block.index, block.previousHash, str(block.timestamp), block.data, block.currentHash, block.proof]
            blockchainList.append(blockList)
        with open(g_bcFileName, "w", newline='') as file: ## 갱신한 블록으로 파일 새로 만듬.
            writer = csv.writer(file)
            writer.writerows(blockchainList)
        # [END] save it to csv
        return 1

def initSvr():
    print("init Server")
    # 1. check if we have a node list file
    last_line_number = row_count(g_nodelstFileName) ## nodefilelist.csv 의 row_count
    # if we don't have, let's request node list
    if last_line_number == 0: ## nodelist내용이 없을 때. 현재 우린 없다.
        # get nodes...node 생성하자.
        for key, value in g_nodeList.items(): # g_nodeList = {'127.0.0.1':'8668'}
            URL = 'http://'+key+':'+value+'/node/getNode'
            print(URL) ## http://127.0.0.1:8668/node/getNode
            try:
                res = requests.get(URL) ## 생성된 url로 요청 보내보기.
            except requests.exceptions.ConnectionError:
                continue
            if res.status_code == 200 : ## 정상이면 밑에 내용을 수행하는데, 현재는 페이지가 안들어가진다. 그러니 addNode 실행 안됌.
                print(res.status_code)
                print(res.text) ## res 출력 후
                tmpNodeLists = json.loads(res.text) ## 해당 key:value를 tempNodeLists에 담고
                for node in tmpNodeLists:
                    addNode(node) ## addNode 함수를 통해 해당 내용 추가.

    # 2. check if we have a blockchain data file
    last_line_number = row_count(g_bcFileName) ## 줄 전체를 읽어오는 함수. blockchain.csv파일의 총 블록 수라고 생각. 블록체인 파일이 있다면 실행된다.
    blockchainList=[]
    if last_line_number == 0: ## 파일은 있고, 블록은 없을 때.
        # get Block Data...
        for key, value in g_nodeList.items(): ## 노드리스트 파일에서 ip, port번호 뽑고 url에 담는다.
            URL = 'http://'+key+':'+value+'/block/getBlockData' ## getBlockData -> readBlockData에서 블록이 없으니 -> generateGenesisBlock() 호출
            try:
                res = requests.get(URL) ## url로 요청 보내기.
            except requests.exceptions.ConnectionError:
                continue
            if res.status_code == 200 :
                print(res.text)
                tmpbcData = json.loads(res.text) ## 제네시스 블록 데이터 받기.
                for line in tmpbcData: ## 반복문으로 추가.
                    # print(type(line))
                    # index, previousHash, timestamp, data, currentHash, proof
                    block = [line['index'], line['previousHash'], line['timestamp'], line['data'],line['currentHash'], line['proof']]
                    blockchainList.append(block)
                try:
                    with open(g_bcFileName, "w", newline='') as file: ## blockChain.csv 파일 새로 갱신.
                        writer = csv.writer(file)
                        writer.writerows(blockchainList)
                except Exception as e:
                    print("file write error in initSvr() "+e)

    return 1

# This class will handle any incoming request from
# a browser
class myHandler(BaseHTTPRequestHandler):

    #def __init__(self, request, client_address, server):
    #    BaseHTTPRequestHandler.__init__(self, request, client_address, server)

    # Handler for the GET requests
    def do_GET(self):
        data = []  # response json data
        if None != re.search('/block/*', self.path):
            if None != re.search('/block/getBlockData', self.path):
               # 20190605 / (kyuin Park, jiweon Lim, sunghoon Oh, sol Han )
               # TODO : http://localhost:8666/block/getBlockData?from=1&end=10 -> from, end 문자열 검사
               # 블록체인 갯수와 맞지 않는 경우 예외 처리 (예> 블록이 4개 존재, 요청은 10개)
               # # 블록 요청 from에 음수값, 0값 예외 처리
               # queryString = urlparse(self.path).query.split('&')
               # startPoint = int(queryString[0].split('=')[1]) - 1
               # endPoint = int(queryString[1].split('=')[1])

                try:
                    self.send_response(200)
                    self.send_header('Content-type', 'application/json')
                    self.end_headers()

                    block = readBlockchain(g_bcFileName, mode = 'external')
                    if block == None: ## 블록이 없는 경우
                        print("No Block Exists")
                        data.append("no data exists")
                    else: ## 블록이 있는 경우
                       for i in range(startPoint, endPoint):
                           print(block[i].__dict__)
                           data.append(block[i].__dict__)

                         for i in block: ## 블록 데이터 data배열에 append.
                             print(i.__dict__)
                             data.append(i.__dict__)


                except:
                    self.send_response(500)
                    self.send_header('Content-type', 'application/json')
                    self.end_headers()
                    data.append("error")
                finally:
                    self.wfile.write(bytes(json.dumps(data, sort_keys=True, indent=4), "utf-8")) ## 블록정보가 담긴 data 배열 dumps.

            elif None != re.search('/block/generateBlock', self.path): ## generateBlock. newtx를 통해 받은 txData.csv의 0인덱스 거래정보를 블록으로 확정시킨다.
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                t = threading.Thread(target=mine)
                t.start()
                data.append("{mining is underway:check later by calling /block/getBlockData}") ## 채굴중이니 나중에 getBlockDaTa로 데이터 받아봐!..
                self.wfile.write(bytes(json.dumps(data, sort_keys=True, indent=4), "utf-8")) ## 제이슨 형식으로 파일 보내주기.
            else:
                self.send_response(404)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                data.append("{info:no such api}")
                self.wfile.write(bytes(json.dumps(data, sort_keys=True, indent=4), "utf-8"))

        elif None != re.search('/node/*', self.path): ## 노드 추가 함수.

            if None != re.search('/node/addNode', self.path):
                queryStr = urlparse(self.path).query.split(':')
                print("client ip : "+self.client_address[0]+" query ip : "+queryStr[0]) ## ip,port를 url로 받아서 노드에 추가시킨다.
                if self.client_address[0] != queryStr[0]: ## 서로의 ip가 다를 때
                    self.send_response(500)
                    self.send_header('Content-type', 'application/json')
                    self.end_headers()
                    data.append("your ip address doesn't match with the requested parameter")
                else: ## 같을 때
                    try:
                        res = addNode(queryStr) ## 해당 ip, port 추가. addnNode 함수 return 값에 따라 아래 finally문 수행.
                    except:
                        pass
                    finally:
                        if res == 1: ## 노드가 정상적으로 추가됬을때.
                            self.send_response(200)
                            self.send_header('Content-type', 'application/json')
                            self.end_headers()
                            importedNodes = readNodes(g_nodelstFileName)
                            data =importedNodes  ## data 덮어쓰기.
                            print("node added okay")
                        elif res == 0 : ## 이도 저도 아닌 예외오류
                            self.send_response(500)
                            self.send_header('Content-type', 'application/json')
                            self.end_headers()
                            data.append("caught exception while saving")
                        elif res == -1 :  ## 이미 있는 node인 경우.
                            self.send_response(500)
                            self.send_header('Content-type', 'application/json')
                            self.end_headers()
                            importedNodes = readNodes(g_nodelstFileName)
                            data = importedNodes
                            data.append("requested node is already exists")
                        self.wfile.write(bytes(json.dumps(data, sort_keys=True, indent=4), "utf-8"))

            elif None != re.search('/node/getNode', self.path): ## getNode Url
                try:
                    importedNodes = readNodes(g_nodelstFileName) ## nodlist.csv 파일 읽어오기
                    data = importedNodes ## data 배열에 node 정보 담기.
                except: ## 오류
                    data.append("error")
                    self.send_response(500)
                    self.send_header('Content-type', 'application/json')
                    self.end_headers()
                else: ## 정상
                    self.send_response(200)
                    self.send_header('Content-type', 'application/json')
                    self.end_headers()
                finally:
                    self.wfile.write(bytes(json.dumps(data, sort_keys=True, indent=4), "utf-8")) ## node 정보 dumps.

        else: ## 404 not bound
                self.send_response(404)
                self.send_header('Content-type', 'application/json')
                self.end_headers()


        # ref : https://mafayyaz.wordpress.com/2013/02/08/writing-simple-http-server-in-python-with-rest-and-json/

    def do_POST(self): ## POST 방식.

        if None != re.search('/block/*', self.path):
            self.send_response(200)
            self.send_header('Content-type', 'application/json')
            self.end_headers()

            if None != re.search('/block/validateBlock/*', self.path): ## 블록 타당성 검증..normal or abnormal.
                ctype, pdict = cgi.parse_header(self.headers['content-type']) ## url 뒤의 ctype, pdict받아오고.
                #print(ctype) #print(pdict)

                if ctype == 'application/json':
                    content_length = int(self.headers['Content-Length'])
                    post_data = self.rfile.read(content_length) ## self.rfile.read 요청한 내용의 모든 본문을 포함한다는 것.
                    receivedData = post_data.decode('utf-8')
                    print(type(receivedData))
                    tempDict = json.loads(receivedData)  # load your str into a list #print(type(tempDict))
                    if isValidChain(tempDict) == True :
                        tempDict.append("validationResult:normal")
                        self.wfile.write(bytes(json.dumps(tempDict), "utf-8")) ## body에 내용 보내기.
                    else :
                        tempDict.append("validationResult:abnormal")
                        self.wfile.write(bytes(json.dumps(tempDict), "utf-8"))
            elif None != re.search('/block/newtx', self.path): ## 해당 경로로 post방식으로 들어올 때.
                ctype, pdict = cgi.parse_header(self.headers['content-type']) ## 헤더의 내용 받아오기.
                if ctype == 'application/json': ## 제이슨일때.
                    content_length = int(self.headers['Content-Length'])
                    post_data = self.rfile.read(content_length) ## self.rfile.read 요청한 내용의 모든 본문을 포함한다는 것.
                    receivedData = post_data.decode('utf-8')
                    print(type(receivedData))
                    tempDict = json.loads(receivedData) ## 해당 데이터 키와 밸류로 받기.
                    res = newtx(tempDict) ## 받은 키와 밸류를 newtx로 넣기.
                    if  res == 1 : ## 정상적일때
                        tempDict.append("accepted : it will be mined later")
                        self.wfile.write(bytes(json.dumps(tempDict), "utf-8"))
                    elif res == -1 : ## 5개 초과했을 때
                        tempDict.append("declined : number of request txData exceeds limitation")
                        self.wfile.write(bytes(json.dumps(tempDict), "utf-8"))
                    elif res == -2 : ## 추가될 데이터가 없을 때
                        tempDict.append("declined : error on data read or write")
                        self.wfile.write(bytes(json.dumps(tempDict), "utf-8"))
                    else : ## 데이터가 정상적이지 않을 때
                        tempDict.append("error : requested data is abnormal")
                        self.wfile.write(bytes(json.dumps(tempDict), "utf-8"))

        elif None != re.search('/node/*', self.path): ## /node/receiveNewBlock 로 post 했을 때.
            self.send_response(200)
            self.send_header('Content-type', 'application/json')
            self.end_headers()
            if None != re.search(g_receiveNewBlock, self.path): # /node/receiveNewBlock
                content_length = int(self.headers['Content-Length'])
                post_data = self.rfile.read(content_length)
                receivedData = post_data.decode('utf-8')
                tempDict = json.loads(receivedData)  # load your str into a list
                print(tempDict) ## body 실려온 내용 print.
                res = compareMerge(tempDict) ## 새 블록 받아서 비교, 병합하는 함수 실행. 추가된 블록이 하나일때만 수행되기에 하자가 많다(내생각). compareMerge함수 호출.
                if res == -1: # internal error
                    tempDict.append("internal server error") ## 서버에러
                elif res == -2 : # block chain info incorrect
                    tempDict.append("block chain info incorrect") ## 서로의 블록 정보가 다른경우.
                elif res == 1: #normal(추가된 블록이 하나만 있는 경우 추가)
                    tempDict.append("accepted")
                elif res == 2: # identical
                    tempDict.append("already updated") ## 이미 있는 데이터인 경우.
                elif res == 3: # we have a longer chain
                    tempDict.append("we have a longer chain") ## 우리가 가지고 있는 데이터가 더 큰 경우.
                self.wfile.write(bytes(json.dumps(tempDict), "utf-8")) ## tempDict dumps.
        else:
            self.send_response(404)
            self.send_header('Content-Type', 'application/json')
            self.end_headers()

        return

class ThreadedHTTPServer(ThreadingMixIn, HTTPServer):
    """Handle requests in a separate thread."""

try:

    # Create a web server and define the handler to manage the
    # incoming request
    # server = HTTPServer(('', PORT_NUMBER), myHandler)
    server = ThreadedHTTPServer(('', PORT_NUMBER), myHandler)
    print('Started httpserver on port ', PORT_NUMBER)

    initSvr()
    # Wait forever for incoming http requests
    server.serve_forever()

except (KeyboardInterrupt, Exception) as e:
    print('^C received, shutting down the web server')
    print(e)
    server.socket.close()